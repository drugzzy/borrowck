use borrowck;
use env::{Environment, Point};
use errors::ErrorReporting;
use loans_in_scope::LoansInScope;
use liveness::Liveness;
use infer::{InferenceContext, RegionVariable};
use nll_repr::repr::{self, RegionName, Variance, RegionDecl};
use std::collections::HashMap;
use std::error::Error;
use region::Region;

pub fn region_check(env: &Environment) -> Result<(), Box<Error>> {
    let ck = &mut RegionCheck {
        env,
        infer: InferenceContext::new(),
        region_map: HashMap::new(),
    };
    ck.check()
}

pub struct RegionCheck<'env> {
    env: &'env Environment<'env>,
    infer: InferenceContext,
    region_map: HashMap<repr::RegionName, RegionVariable>,
}

impl<'env> RegionCheck<'env> {
    pub fn env(&self) -> &'env Environment<'env> {
        self.env
    }

    pub fn region(&self, name: RegionName) -> &Region {
        let var = match self.region_map.get(&name) {
            Some(&var) => var,
            None => panic!("no region variable ever created with name `{:?}`", name),
        };
        self.infer.region(var)
    }

    // borrowck的核心函数
    fn check(&mut self) -> Result<(), Box<Error>> {
        let mut errors = ErrorReporting::new();

        // Register expected errors.
        // 这里应该是为了验证测试用例而写的，实际没啥用
        for &block in &self.env.reverse_post_order {
            let actions = self.env.graph.block_data(block).actions();
            for (index, action) in actions.iter().enumerate() {
                let point = Point { block, action: index };
                if let Some(ref expected) = action.should_have_error {
                    errors.expect_error(point, &expected.string);
                }
            }
        }

        // Compute liveness.
        // 计算liveness
        let liveness = &Liveness::new(self.env);

        // Add inference constraints.
        // 根据上面算的liveness，添加约束，还有subtyping约束和reborrow约束
        self.populate_inference(liveness);

        // 约束求解，迭代到不动点
        // Solve inference constraints, reporting any errors.
        // 有可能要在约束求解的过程中报错？主要是capped场景
        for error in self.infer.solve(self.env) {
            errors.report_error(error.constraint_point,
                                format!("capped variable `{}` exceeded its limits",
                                        error.name));
        }

        // Compute loans in scope at each point.
        let loans_in_scope = &LoansInScope::new(self);

        // Run the borrow check, reporting any errors.
        borrowck::borrow_check(self.env, loans_in_scope, &mut errors);

        // Check that all assertions are obeyed.
        self.check_assertions(liveness)?;

        // Check that we found the errors we expect to.
        errors.reconcile_errors()
    }

    fn check_assertions(&self, liveness: &Liveness) -> Result<(), Box<Error>> {
        let mut errors = 0;

        for assertion in self.env.graph.assertions() {
            match *assertion {
                repr::Assertion::Eq(region_name, ref region_literal) => {
                    let region_var = self.region_map[&region_name];
                    let region_value = self.to_region(region_literal);
                    if *self.infer.region(region_var) != region_value {
                        errors += 1;
                        println!("error: region variable `{:?}` has wrong value", region_name);
                        println!("  expected: {:?}", region_value);
                        println!("  found   : {:?}", self.infer.region(region_var));
                    }
                }

                repr::Assertion::In(region_name, ref point) => {
                    let region_var = self.region_map[&region_name];
                    let point = self.to_point(point);
                    if !self.infer.region(region_var).may_contain(point) {
                        errors += 1;
                        println!(
                            "error: region variable `{:?}` does not contain `{:?}`",
                            region_name,
                            point
                        );
                        println!("  found   : {:?}", self.infer.region(region_var));
                    }
                }

                repr::Assertion::NotIn(region_name, ref point) => {
                    let region_var = self.region_map[&region_name];
                    let point = self.to_point(point);
                    if self.infer.region(region_var).may_contain(point) {
                        errors += 1;
                        println!(
                            "error: region variable `{:?}` contains `{:?}`",
                            region_name,
                            point
                        );
                        println!("  found   : {:?}", self.infer.region(region_var));
                    }
                }

                repr::Assertion::Live(var, block_name) => {
                    let block = self.env.graph.block(block_name);
                    if !liveness.var_live_on_entry(var, block) {
                        errors += 1;
                        println!(
                            "error: variable `{:?}` not live on entry to `{:?}`",
                            var,
                            block_name
                        );
                    }
                }

                repr::Assertion::NotLive(var, block_name) => {
                    let block = self.env.graph.block(block_name);
                    if liveness.var_live_on_entry(var, block) {
                        errors += 1;
                        println!(
                            "error: variable `{:?}` live on entry to `{:?}`",
                            var,
                            block_name
                        );
                    }
                }

                repr::Assertion::RegionLive(region_name, block_name) => {
                    let block = self.env.graph.block(block_name);
                    if !liveness.region_live_on_entry(region_name, block) {
                        errors += 1;
                        println!(
                            "error: region `{:?}` not live on entry to `{:?}`",
                            region_name,
                            block_name
                        );
                    }
                }

                repr::Assertion::RegionNotLive(region_name, block_name) => {
                    let block = self.env.graph.block(block_name);
                    if liveness.region_live_on_entry(region_name, block) {
                        errors += 1;
                        println!(
                            "error: region `{:?}` live on entry to `{:?}`",
                            region_name,
                            block_name
                        );
                    }
                }
            }
        }

        if errors > 0 {
            try!(Err(format!("{} errors found", errors)));
        }

        Ok(())
    }

    // 还不懂，目测是对named lifetimes做的
    fn populate_outlives(
        &mut self,
        rv: RegionVariable,
        visited: &mut Vec<RegionName>, // memoization
        outlives: &Vec<RegionName>,
    ) {
        for &region in outlives {
            // avoid recomputation
            if visited.contains(&region) {
                continue;
            }

            let skolemized_block = self.env.graph.skolemized_end(region);
            self.infer.add_live_point(rv, Point { block: skolemized_block,  action: 0, });
            let outlives = {
                let mut possible_matches = self.env.graph
                    .free_regions()
                    .iter()
                    .filter(|rd| region == rd.name);
                match possible_matches.next() {
                    Some(region_decl) => &region_decl.outlives,
                    None => continue
                }
            };

            visited.push(region);
            self.populate_outlives(rv, visited, &outlives);
        }
    }

    // 添加约束
    fn populate_inference(&mut self, liveness: &Liveness) {
        // This is sort of a hack, but... for each "free region" `r`,
        // we will wind up with a region variable. We want that region
        // variable to be inferred to precisely the set: `{G, ...,
        // End(r)}`, where `G` is all the points in the control-flow
        // graph, and `End(r)` is the end-point of `r`. We also want
        // to include the endpoints of any free-regions that `r`
        // outlives. We're not enforcing (in inference) that `r` doesn't
        // get inferred to some *larger* region (that would be a kind of
        // constraint we would need to add, and inference right now
        // doesn't permit such constraints -- you could also view it
        // an assertion that we add to the tests).
        // 这里应该是先处理free region
        for region_decl in self.env.graph.free_regions() {
            let &RegionDecl{ name: region, ref outlives } = region_decl;
            let rv = self.region_variable(region);
            for &block in &self.env.reverse_post_order {
                let end_point = self.env.end_point(block);
                // cfg的每个节点都是free region活着的地方
                for action in 0 .. end_point.action {
                    self.infer.add_live_point(rv, Point { block, action });
                }
                self.infer.add_live_point(rv, end_point);
            }

            // 加上end('r)这种位置
            let skolemized_block = self.env.graph.skolemized_end(region);
            self.infer.add_live_point(rv, Point { block: skolemized_block, action: 0 });
            // 这里还没看懂
            self.populate_outlives(rv, &mut vec![region], outlives);
            self.infer.cap_var(rv);
            log!("Region for {:?}:\n{:#?}\n", region, self.infer.region(rv));
        }

        // 在这里遍历一遍是为了一次性添加liveness约束、subtyping约束和reborrow约束
        liveness.walk(|point, action, live_on_entry| {
            // To start, find every variable `x` that is live. All regions
            // in the type of `x` must include `point`.
            // liveness用的是在每个point的infact
            // 这里是真正根据liveness来添加liveness约束的地方
            for region_name in liveness.live_regions(live_on_entry) {
                let rv = self.region_variable(region_name);
                self.infer.add_live_point(rv, point);
            }

            let action = if let Some(action) = action {
                action
            } else {
                return;
            };

            // Next, walk the actions and establish any additional constraints
            // that may arise from subtyping.
            // subtyping和reborrow都是在后继生效，所以需要这个
            // 如果是terminator怎么办？
            // 有可能没影响，因为这个变量只会用在subtyping和reborrow中，而这俩情况不可能是terminator
            let successor_point = Point {
                block: point.block,
                action: point.action + 1,
            };
            match action.kind {
                // `p = &'x` -- first, `'x` must include this point @ P,
                // and second `&'x <: typeof(p) @ succ(P)`
                repr::ActionKind::Borrow(
                    ref dest_path,
                    region_name,
                    borrow_kind,
                    ref source_path,
                ) => {
                    // p的类型
                    let dest_ty = self.env.path_ty(dest_path);
                    let source_ty = self.env.path_ty(source_path);
                    // RHS的类型，这个场景下RHS一定是一个引用类型
                    let ref_ty = Box::new(repr::Ty::Ref(
                        repr::Region::Free(region_name),
                        borrow_kind,
                        source_ty,
                    ));
                    // dest_ty是ref_ty的subtype，即ref_ty: dest_ty @ P
                    // 感觉这里传Co，然后把dest_ty和ref_ty换一下位置也没问题，跑了测试套试了一下，用例还是都通过的
                    // self.relate_tys(successor_point, repr::Variance::Co, &ref_ty, &dest_ty);
                    self.relate_tys(successor_point, repr::Variance::Contra, &dest_ty, &ref_ty);
                    // 添加可能存在的reborrow约束
                    self.ensure_borrow_source(successor_point, region_name, source_path);
                }

                // a = b
                // 这里不用处理reborrow，因为b一定是个lvalue，reborrow只会在上面那个case中处理
                // assign这个场景包含两个引用类型之间assign，也包含结构体之间的assign，且结构体有引用类型的成员
                repr::ActionKind::Assign(ref a, ref b) => {
                    // 拿到path的类型，好像没什么特别的
                    let a_ty = self.env.path_ty(a);
                    let b_ty = self.env.path_ty(b);

                    // `b` must be a subtype of `a` to be assignable:
                    // b要比a活得长，协变，b: a @ P
                    self.relate_tys(successor_point, repr::Variance::Co, &b_ty, &a_ty);
                }

                // 'X: 'Y
                // 应该是where约束
                repr::ActionKind::Constraint(ref c) => {
                    match **c {
                        repr::Constraint::Outlives(c) => {
                            let sup_v = self.region_variable(c.sup);
                            let sub_v = self.region_variable(c.sub);
                            self.infer.add_outlives(sup_v, sub_v, point);
                        }
                        _ => {
                            panic!("unimplemented rich constraint: {:?}", c);
                        }
                    }
                }

                // 这些都不用处理
                // 为什么Init不用处理，感觉Init跟Assign的区别不大，还不懂
                // 对于函数调用返回借用的情况，不知道是怎么处理的，感觉是需要处理的，但这里简化了
                repr::ActionKind::Init(..) |
                repr::ActionKind::Use(..) |
                repr::ActionKind::Drop(..) |
                repr::ActionKind::StorageDead(..) |
                repr::ActionKind::SkolemizedEnd(_) |
                repr::ActionKind::Noop => {
                    // no add'l constriants needed here; basic liveness
                    // suffices.
                }
            }
        });
    }

    fn region_variable(&mut self, n: repr::RegionName) -> RegionVariable {
        let infer = &mut self.infer;
        let r = *self.region_map.entry(n).or_insert_with(|| infer.add_var(n));
        log!("{:?} => {:?}", n, r);
        r
    }

    fn to_point(&self, point: &repr::Point) -> Point {
        let block = match point.block {
            repr::PointName::Code(b) => self.env.graph.block(b),
            repr::PointName::SkolemizedEnd(r) => self.env.graph.skolemized_end(r),
        };
        Point {
            block: block,
            action: point.action,
        }
    }

    // 看着没啥用，好像是assert判断时候用的
    fn to_region(&self, user_region: &repr::RegionLiteral) -> Region {
        let mut region = Region::new();
        for p in &user_region.points {
            region.add_point(self.to_point(p));
        }
        region
    }

    // 应该是解析subtyping的关系创建对应的约束
    fn relate_tys(
        &mut self,
        successor_point: Point,
        variance: repr::Variance,
        a: &repr::Ty,
        b: &repr::Ty,
    ) {
        log!(
            "relate_tys({:?} {:?} {:?} @ {:?})",
            a,
            variance,
            b,
            successor_point
        );
        match (a, b) {
            // 两个引用类型之间赋值，比如p = q，还有p = &mut local
            (&repr::Ty::Ref(r_a, bk_a, ref t_a), &repr::Ty::Ref(r_b, bk_b, ref t_b)) => {
                assert_eq!(bk_a, bk_b, "cannot relate {:?} and {:?}", a, b);
                // 创建当前层级的region之间的约束
                self.relate_regions(
                    successor_point,
                    variance.invert(), // 要倒置一下，感觉是a和b参数顺序导致的
                    r_a.assert_free(),
                    r_b.assert_free(),
                );
                // 递归里面的子类型，即被借用的类型
                // 对毕昇C，就不需要了，因为没有对借用取借用
                // 先拿到被借用的类型的variance
                let referent_variance = variance.xform(bk_a.variance());
                // t_a和t_b就是被借用的类型，因此要递归进去
                self.relate_tys(successor_point, referent_variance, t_a, t_b);
            }
            (&repr::Ty::Unit, &repr::Ty::Unit) => {}
            // p = q，但p和q都是struct类型，应该是这样
            // 这里还没看是怎么做的
            (&repr::Ty::Struct(s_a, ref ps_a), &repr::Ty::Struct(s_b, ref ps_b)) => {
                if s_a != s_b {
                    panic!("cannot compare `{:?}` and `{:?}`", s_a, s_b);
                }
                let s_decl = self.env.struct_map[&s_a];
                if ps_a.len() != s_decl.parameters.len() {
                    panic!("wrong number of parameters for `{:?}`", a);
                }
                if ps_b.len() != s_decl.parameters.len() {
                    panic!("wrong number of parameters for `{:?}`", b);
                }
                for (sp, (p_a, p_b)) in s_decl.parameters.iter().zip(ps_a.iter().zip(ps_b)) {
                    let v = variance.xform(sp.variance);
                    self.relate_parameters(successor_point, v, p_a, p_b);
                }
            }
            _ => {
                panic!(
                    "cannot relate types `{:?}` and `{:?}` at {:?}",
                    a,
                    b,
                    successor_point
                )
            }
        }
    }

    fn relate_regions(
        &mut self,
        successor_point: Point,
        variance: repr::Variance,
        a: repr::RegionName,
        b: repr::RegionName,
    ) {
        log!(
            "relate_regions({:?} {:?} {:?} @ {:?})",
            a,
            variance,
            b,
            successor_point
        );
        let r_a = self.region_variable(a);
        let r_b = self.region_variable(b);
        match variance {
            Variance::Co =>
                // "a Co b" == "a <= b"
                self.infer.add_outlives(r_b, r_a, successor_point),
            Variance::Contra =>
                // "a Contra b" == "a >= b"
                self.infer.add_outlives(r_a, r_b, successor_point),
            Variance::In => {
                // 对于invariance，需要加两条约束
                self.infer.add_outlives(r_a, r_b, successor_point);
                self.infer.add_outlives(r_b, r_a, successor_point);
            }
        }
    }

    fn relate_parameters(
        &mut self,
        successor_point: Point,
        variance: repr::Variance,
        a: &repr::TyParameter,
        b: &repr::TyParameter,
    ) {
        match (a, b) {
            (&repr::TyParameter::Ty(ref t_a), &repr::TyParameter::Ty(ref t_b)) => {
                self.relate_tys(successor_point, variance, t_a, t_b)
            }
            (&repr::TyParameter::Region(r_a), &repr::TyParameter::Region(r_b)) => {
                self.relate_regions(
                    successor_point,
                    variance,
                    r_a.assert_free(),
                    r_b.assert_free(),
                )
            }
            _ => panic!("cannot relate parameters `{:?}` and `{:?}`", a, b),
        }
    }

    /// Add any relations between regions that are needed to ensures
    /// that reborrows live long enough. Specifically, if we borrow
    /// something like `*r` for `'a`, where `r: &'b i32`, then `'b:
    /// 'a` is required.
    /// 这看着像处理reborrow，好像还真是，下面有supporting prefixes
    /// &'a *lv，lv的生命周期为'b，则'b : 'a @ P
    fn ensure_borrow_source(
        &mut self,
        successor_point: Point,
        borrow_region_name: RegionName,
        source_path: &repr::Path,
    ) {
        log!(
            "ensure_borrow_source({:?}, {:?}, {:?})",
            successor_point,
            borrow_region_name,
            source_path
        );

        for supporting_path in self.env.supporting_prefixes(source_path) {
            match *supporting_path {
                repr::Path::Var(_) => {
                    // No lifetime constraints are needed to ensure the
                    // validity of a variable. That is ensured by borrowck
                    // preventing the storage of variables from being killed
                    // while data owned by that variable is in scope.
                    return;
                }
                repr::Path::Extension(ref base_path, field_name) => {
                    let ty = self.env.path_ty(base_path);
                    log!("ensure_borrow_source: ty={:?}", ty);
                    match *ty {
                        // 这里还不太懂，虽然知道是对*b生成reborrow约束
                        // 这里不用递归是因为for循环里处理了所有supporting prefixes，所以没必要递归
                        repr::Ty::Ref(ref_region, _, _) => {
                            assert_eq!(field_name, repr::FieldName::star());
                            let ref_region_name = ref_region.assert_free();
                            let borrow_region_variable = self.region_variable(borrow_region_name);
                            let ref_region_variable = self.region_variable(ref_region_name);
                            self.infer.add_outlives(
                                ref_region_variable,
                                borrow_region_variable,
                                successor_point,
                            );
                        }
                        repr::Ty::Unit => {}
                        repr::Ty::Struct(..) => {}
                        repr::Ty::Bound(..) => {}
                    }
                }
            }
        }
    }
}
