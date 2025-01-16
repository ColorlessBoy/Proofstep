# Proofstep

This is a tactic called `proofstep`.
By using this tactic, the proof process becomes more like a dialogue, making it more intuitive and accessible, especially for training Large Language Models.

```lean
theorem test1 : (α : Prop) -> Iff α α := by
  -- goal : (α : Prop) -> Iff α α
  proofstep (fun (α : Prop) => @Iff.intro α α)
  -- action : (α : Prop) -> (α -> α) -> (α -> α) -> (α <-> α)
  -- goal : (α : Prop) -> (α -> α) , (α : Prop) -> (α -> α) -> (α -> α)
  proofstep (fun (α : Prop) (h : α) => h)
  -- action : (α : Prop) -> (α -> α) 
  -- goal : (α : Prop) -> (α -> α) -> (α -> α)
  proofstep (fun (α : Prop) (h : α → α ) => h)
  -- action : (α : Prop) -> (α -> α) -> (α -> α) 
  -- goal : Q.E.D.
```