def Plausible.TotalFunction.Pi.sampleableExt.{u, v, ub} : {α : Type u} →
  {β : Type v} →
    [inst : SampleableExt.{u + 1, u} α] →
      [inst : SampleableExt.{v + 1, ub} β] →
        [inst : DecidableEq.{u + 1} α] → [inst : Repr.{u} α] → SampleableExt.{max (u + 1) (v + 1), max ub u} (α → β) :=
fun {α} {β} [SampleableExt.{u + 1, u} α] [SampleableExt.{v + 1, ub} β] [DecidableEq.{u + 1} α] [Repr.{u} α] =>
  SampleableExt.mk.{max (u + 1) (v + 1), max ub u} (TotalFunction.{u, ub} α (SampleableExt.proxy.{v + 1, ub} β))
    (do
      let xs ← SampleableExt.sample.{(max v u) + 1, max u ub}
      let __discr ← Gen.up.{ub, u} SampleableExt.sample.{v + 1, ub}
      match __discr with
        | ULift.up.{u, ub} x =>
          pure.{max u ub, max u ub}
            (withDefault.{u, ub}
              (List.toFinmap'.{u, ub}
                (List.map.{max ub u, max u ub} (Prod.map.{u, u, ub, ub} SampleableExt.interp.{u + 1, u} id.{ub + 1})
                  xs))
              x))
    fun f => Function.comp.{u + 1, ub + 1, v + 1} SampleableExt.interp.{v + 1, ub} (apply.{u, ub} f)

```lean
xs : List.{max ub u} (Prod.{u, ub} (SampleableExt.proxy.{u + 1, u} α) (SampleableExt.proxy.{v + 1, ub} β))
```