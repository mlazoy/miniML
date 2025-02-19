-- Constraint unification
unify :: Constraints -> Error Substitution
unify [] = return M.empty -- no more rules
unify ((t1, t2, posn):cnstr')   
  | t1 == t2 = unify cnstr'   -- trivial
  | (TVar a) <- t1, not (occursFreeType a t2) = do 
    let subst = M.insert a t1 M.empty;
    lift $ applySubst t2 subst;
    return unify (applySubstCnstr cnstr' subst)
  | (TVar a) <- t2, not (occursFreeType a t1) = do
    let subst = M.insert a t2 M.empty;
    applySubst t1 subst;
    unify (applySubstCnstr cnstr' subst)
  | (TArrow t11 t12) <- t1, (TArrow t21 t22) <- t2 = 
    let c' = (t11, t21, posn) in
      let c'' = (t12, t22, posn) in 
        unify (c' : c'' : cnstr')
  | (TProd t11 t12) <- t1, (TProd t21 t22) <- t2 = 
      let c' = (t11, t21, posn) in
        let c'' = (t12, t22, posn) in 
          unify (c' : c'' : cnstr')
  | (TSum t11 t12) <- t1, (TSum t21 t22) <- t2 = 
      let c' = (t11, t21, posn) in
        let c'' = (t12, t22, posn) in 
          unify (c' : c'' : cnstr')
  | (TList t1) <- t1, (TList t2) <- t2 = 
    let c' = (t1, t2, posn) in 
      unify (c' : cnstr')
  | otherwise = 
    lift $ typeError posn 
      ("Could not unify expression of type " <> showType t1 " with " <> showType t2 <>  ".\n")