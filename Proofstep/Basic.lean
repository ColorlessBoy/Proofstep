import Lean
import Lean.Meta
open Lean Elab Tactic Meta

-- 定义一个辅助函数，用于比较和拆分目标
def proofStep (flag : Expr)
    (action goal: Expr)
    (diffContext sameContext : List (Expr × Expr) := [])
    : MetaM (Option ((List Expr) × Nat)) := do
  -- 添加调试日志
  trace[Meta.debug] "ProofStep called with action: {action}, goal: {goal}"
  trace[Meta.debug] "Current diffContext: {diffContext}, sameContext: {sameContext}"

  if ← Meta.isDefEq action goal then
    trace[Meta.debug] "Action and goal are definitionally equal"
    let mut newGoals: List Expr := []
    for (fvar, ctxType) in diffContext.reverse do
      trace[Meta.debug] "Processing diffContext: {ctxType}"
      newGoals ← newGoals.mapM (fun g => mkForallFVars #[fvar] g)
      newGoals := ctxType :: newGoals
    trace[Meta.debug] "Processing sameContext"
    let sameFVars := (sameContext.map (fun (fvar, _)=>fvar)).toArray
    newGoals ← newGoals.mapM (fun g => mkForallFVars sameFVars g)
    trace[Meta.debug] "New goals: {newGoals}"
    return some (newGoals, sameFVars.size)

  match flag with
  | Expr.forallE _ _ flagBody _ =>
    match action with
    | Expr.forallE name ty body info =>
      trace[Meta.debug] "Action is a forall with name: {name}, type: {ty}"
      if diffContext.isEmpty then
        match goal with
        | Expr.forallE _ goalTy goalBody _ =>
          trace[Meta.debug] "Goal is also a forall with type: {goalTy}"
          -- 对 body 进行比较时，确保绑定变量一致
          if ← Meta.isDefEq ty goalTy then
            trace[Meta.debug] "Action and goal have same argument type."
            withLocalDecl name info ty fun fVar => do
              -- 递归调用 proofStep
              let action := body.instantiate1 fVar
              let goal := goalBody.instantiate1 fVar
              return ← proofStep flagBody action goal diffContext (sameContext ++ [⟨fVar, ty⟩])
          else
            trace[Meta.debug] "Action and goal have different argument type."
            withLocalDecl name info ty fun fVar => do
              let action := body.instantiate1 fVar
              return ← proofStep flagBody action goal (diffContext ++ [⟨fVar, ty⟩]) sameContext
        | _ =>
          trace[Meta.debug] "Goal is not a forall"
          withLocalDecl name info ty fun fVar => do
            let action := body.instantiate1 fVar
            return ← proofStep flagBody action goal (diffContext ++ [⟨fVar, ty⟩]) sameContext
      else
        trace[Meta.debug] "Adding to diffContext"
        withLocalDecl name info ty fun fVar => do
          let action := body.instantiate1 fVar
          return ← proofStep flagBody action goal (diffContext ++ [⟨fVar, ty⟩]) sameContext
    | _ =>
      trace[Meta.debug] "Action is not a forall"
      return none
  | _ =>
      trace[Meta.debug] "Flag is not a forall"
      return none

def postProcess (depth: Nat) (sameFVars : List Expr) (action: Expr) (oriAction: Expr) (solutionMVarIds : List MVarId) : MetaM (Option Expr) := do
  match depth with
  | Nat.zero =>
    let solutions := solutionMVarIds.map (Expr.mvar)
    trace[Meta.debug] "Collected solutions: {solutionMVarIds}"
    -- 组装最终证明项
    let mut partSolutions : List Expr := []
    for solution in solutions do
      let mut g : Expr := solution
      for fvar in sameFVars do
        g := mkApp g fvar
      for solution in partSolutions do
        g := mkApp g solution
      partSolutions := partSolutions ++ [g]
    let mut rst := oriAction
    for fvar in sameFVars do
      rst := mkApp rst fvar
    for solution in partSolutions do
      rst := mkApp rst solution
    rst ← mkLambdaFVars sameFVars.toArray rst
    trace[Meta.debug] "Rst: {rst}"
    return some rst
  | Nat.succ preDepth =>
    match action with
    | Expr.lam name ty body info =>
      withLocalDecl name info ty fun fVar => do
        let body := body.instantiate1 fVar
        return ← postProcess preDepth (sameFVars ++ [fVar]) body oriAction solutionMVarIds
    | _ =>
      trace[Meta.debug] "Action is not a lambda"
      return none

-- 定义 tactic，封装 proofStep 的逻辑
syntax (name := proofStepTactic) "proofstep " term : tactic

@[tactic proofStepTactic] def evalProofStepTactic : Tactic := fun stx =>
  match stx with
  | `(tactic| proofstep $actionExpr) => do
    -- 获取当前目标
    let mainGoal ← getMainGoal
    let goal ← mainGoal.getType

    -- 解析 action 表达式
    let action ← elabTerm actionExpr none
    let actionType ← inferType action

    -- 调用 proofStep
    match ← proofStep actionType actionType goal with
    | some (newGoals, depth) =>
      if newGoals.isEmpty then
        -- 如果目标已被证明，表示成功结束
        trace[Meta.debug] "Goal proven successfully."
        mainGoal.assign action
        replaceMainGoal []
      else
        -- 替换目标并设置新目标
        let newGoalMVarExprs ← newGoals.mapM (fun type => mkFreshExprMVar (some type))
        let newGoalMVarIds := newGoalMVarExprs.map (Expr.mvarId!)
        trace[Meta.debug] "newGoalMVarIds {newGoalMVarIds}"
        replaceMainGoal newGoalMVarIds
        withMainContext do
          match ← postProcess depth [] action action newGoalMVarIds with
          | some solution =>
            mainGoal.assign solution
          | _ =>
            throwError "PostProcess failed."
    | none =>
      throwError "Failed to abstract the proof step. Ensure action and goal are compatible."
  | _ => throwUnsupportedSyntax
