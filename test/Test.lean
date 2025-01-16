import Proofstep

theorem test1 : (α : Prop) -> Iff α α := by
  proofstep (fun (α : Prop) => @Iff.intro α α)
  proofstep (fun (α : Prop) (h : α) => h)
  proofstep (fun (α : Prop) (h : α → α ) => h)
