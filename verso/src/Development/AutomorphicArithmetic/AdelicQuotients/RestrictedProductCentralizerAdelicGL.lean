import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

/- English proof (translation)
Introduce `V G Gi Gv _ _ _ _ _ _ _ _ _ _ _ _ q p K h g`. Establish `comm : ∀ {A : Type} [Group A] {a b : A}, b ∈ Subgroup.centralizer ({a} : Set A) ↔ a * b = b * a`. Introduce `A _ a b`. Rewrite using `[Subgroup.mem_centralizer_singleton_iff]`. Conclude with `⟨fun e => e.symm, fun e => e.symm⟩`.

Establish `key : ∀ x : G, q x ∈ Subgroup.centralizer ({q g} : Set Gi) → (∀ v, p v x ∈ Subgroup.centralizer ({p v g} : Set (Gv v))) → x ∈ Subgroup.centralizer ({g} : Set G)`. Introduce `x h1 h2`. Use `comm.2 (h.ext _ _ ?_ fun v => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, map_mul]`. Conclude with `comm.1 h1`.

Rewrite using `[map_mul, map_mul]`. Conclude with `comm.1 (h2 v)`. Use `{ cq := ?_, cp := ?_, opn := ?_, cpt := ?_, ae := ?_, opnU := ?_, ext := ?_, surj := ?_, prop := ?_ }` and prove the remaining obligations. Conclude with `Continuous.subtype_mk (h.cq.comp continuous_subtype_val) _`. Introduce `v`.

Conclude with `Continuous.subtype_mk ((h.cp v).comp continuous_subtype_val) _`. Introduce `v`. Conclude with `(h.opn v).preimage continuous_subtype_val`. Introduce `v`. Establish `hc : IsClosed ((Subgroup.centralizer ({p v g} : Set (Gv v)) : Subgroup (Gv v)) : Set (Gv v))`.

Establish `: ((Subgroup.centralizer ({p v g} : Set (Gv v)) : Subgroup (Gv v)) : Set (Gv v)) = {x | p v g * x = x * p v g}`. Use extensionality with `x`. Conclude with `comm`. Rewrite using `[this]`. Conclude with `isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)`.

Conclude with `hc.isClosedEmbedding_subtypeVal.isCompact_preimage (h.cpt v)`. Introduce `t`. Conclude with `h.ae t`. Introduce `S`. Conclude with `(h.opnU S).preimage continuous_subtype_val`.

Introduce `a b h1 h2`. Conclude with `Subtype.ext (h.ext _ _ (congrArg Subtype.val h1) fun v => congrArg Subtype.val (h2 v))`. Introduce `gi gv hv`. Take `⟨x, hx, hx'⟩` from `h.surj gi.1 (fun v => (gv v).1) hv`. Use `⟨⟨x, key x (hx ▸ gi.2) fun v => (hx' v).symm ▸ (gv v).2⟩, Subtype.ext hx, fun v => Subtype.ext (hx' v)⟩` and prove the remaining obligations.

Introduce `Ci C hCi hC hae`. Rewrite using `[Subtype.isCompact_iff]`. Establish `e : Subtype.val '' {t : Subgroup.centralizer ({g} : Set G) | cen q g t ∈ Ci ∧ ∀ v, cen (p v) g t ∈ C v} = {x | q x ∈ Subtype.val '' Ci ∧ ∀ v, p v x ∈ Subtype.val '' C v}`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨t, ⟨h1, h2⟩, rfl⟩`. Conclude with `⟨⟨_, h1, rfl⟩, fun v => ⟨_, h2 v, rfl⟩⟩`. Introduce and unpack `⟨⟨a, ha, ea⟩, h2⟩`. Establish `hx : x ∈ Subgroup.centralizer ({g} : Set G)`. Use `key x (ea ▸ a.2) fun v => ?_` and prove the remaining obligations.

Take `⟨b, -, eb⟩` from `h2 v`. Conclude with `eb ▸ b.2`. Use `⟨⟨x, hx⟩, ⟨?_, fun v => ?_⟩, rfl⟩` and prove the remaining obligations. Establish `: cen q g ⟨x, hx⟩ = a` using `Subtype.ext ea.symm`. Rewrite using `[this]`.

Conclude with `ha`. Take `⟨b, hb, eb⟩` from `h2 v`. Establish `: cen (p v) g ⟨x, hx⟩ = b` using `Subtype.ext eb.symm`. Rewrite using `[this]`. Conclude with `hb`.

Rewrite using `[e]`. Use `h.prop _ _ (Subtype.isCompact_iff.1 hCi) (fun v => Subtype.isCompact_iff.1 (hC v)) ?_` and prove the remaining obligations. Use `filter_upwards [hae] with v hv`. Introduce and unpack `_ ⟨b, hb, rfl⟩`. Conclude with `hv hb`.
-/
theorem UpperTheory.restrictedProduct_centralizer_adelicGL :
    RPCen := by
  intro V G Gi Gv _ _ _ _ _ _ _ _ _ _ _ _ q p K h g
  have comm : ∀ {A : Type} [Group A] {a b : A}, b ∈ Subgroup.centralizer ({a} : Set A) ↔ a * b = b * a := by
    intro A _ a b
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun e => e.symm, fun e => e.symm⟩
  have key : ∀ x : G, q x ∈ Subgroup.centralizer ({q g} : Set Gi) →
      (∀ v, p v x ∈ Subgroup.centralizer ({p v g} : Set (Gv v))) →
      x ∈ Subgroup.centralizer ({g} : Set G) := by
    intro x h1 h2
    refine comm.2 (h.ext _ _ ?_ fun v => ?_)
    · rw [map_mul, map_mul]; exact comm.1 h1
    · rw [map_mul, map_mul]; exact comm.1 (h2 v)
  refine
    { cq := ?_, cp := ?_, opn := ?_, cpt := ?_, ae := ?_, opnU := ?_, ext := ?_, surj := ?_, prop := ?_ }
  · exact Continuous.subtype_mk (h.cq.comp continuous_subtype_val) _
  · intro v
    exact Continuous.subtype_mk ((h.cp v).comp continuous_subtype_val) _
  · intro v
    exact (h.opn v).preimage continuous_subtype_val
  · intro v
    have hc : IsClosed ((Subgroup.centralizer ({p v g} : Set (Gv v)) : Subgroup (Gv v)) : Set (Gv v)) := by
      have : ((Subgroup.centralizer ({p v g} : Set (Gv v)) : Subgroup (Gv v)) : Set (Gv v))
          = {x | p v g * x = x * p v g} := by
        ext x; exact comm
      rw [this]
      exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
    exact hc.isClosedEmbedding_subtypeVal.isCompact_preimage (h.cpt v)
  · intro t
    exact h.ae t
  · intro S
    exact (h.opnU S).preimage continuous_subtype_val
  · intro a b h1 h2
    exact Subtype.ext (h.ext _ _ (congrArg Subtype.val h1) fun v => congrArg Subtype.val (h2 v))
  · intro gi gv hv
    obtain ⟨x, hx, hx'⟩ := h.surj gi.1 (fun v => (gv v).1) hv
    refine ⟨⟨x, key x (hx ▸ gi.2) fun v => (hx' v).symm ▸ (gv v).2⟩, Subtype.ext hx, fun v => Subtype.ext (hx' v)⟩
  · intro Ci C hCi hC hae
    rw [Subtype.isCompact_iff]
    have e : Subtype.val '' {t : Subgroup.centralizer ({g} : Set G) | cen q g t ∈ Ci ∧ ∀ v, cen (p v) g t ∈ C v}
        = {x | q x ∈ Subtype.val '' Ci ∧ ∀ v, p v x ∈ Subtype.val '' C v} := by
      ext x
      constructor
      · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
        exact ⟨⟨_, h1, rfl⟩, fun v => ⟨_, h2 v, rfl⟩⟩
      · rintro ⟨⟨a, ha, ea⟩, h2⟩
        have hx : x ∈ Subgroup.centralizer ({g} : Set G) := by
          refine key x (ea ▸ a.2) fun v => ?_
          obtain ⟨b, -, eb⟩ := h2 v
          exact eb ▸ b.2
        refine ⟨⟨x, hx⟩, ⟨?_, fun v => ?_⟩, rfl⟩
        · have : cen q g ⟨x, hx⟩ = a := Subtype.ext ea.symm
          rw [this]; exact ha
        · obtain ⟨b, hb, eb⟩ := h2 v
          have : cen (p v) g ⟨x, hx⟩ = b := Subtype.ext eb.symm
          rw [this]; exact hb
    rw [e]
    refine h.prop _ _ (Subtype.isCompact_iff.1 hCi) (fun v => Subtype.isCompact_iff.1 (hC v)) ?_
    filter_upwards [hae] with v hv
    rintro _ ⟨b, hb, rfl⟩
    exact hv hb
