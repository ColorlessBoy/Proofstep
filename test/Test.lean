import Proofstep

theorem test1 : (α : Prop) -> Iff α α := by
  Proofstep (fun (α : Prop) => @Iff.intro α α)
  Proofstep (fun (α : Prop) (h : α) => h)
  Proofstep (fun (α : Prop) (h : α → α ) => h)
