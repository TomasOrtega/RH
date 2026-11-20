import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LcountNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ModelMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.QuoMulInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.HsCast
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.SymbolEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IndexVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.HsHasse

namespace UpperTheory.V.Z.Sym.Glob

open Classical in
/- English proof (translation)
Establish `hT : {v | ¬(a v = 1 ∧ b v = 0)}.Finite` using `Filter.eventually_cofinite.mp hab`. Use `set T : Finset I := hT.toFinset \ Sg with hTdef`. Establish `hout : ∀ v, v ∉ Sg → v ∉ T → a v = 1 ∧ b v = 0`. Introduce `v h1 h2`. Assume the negation of the conclusion as `h3`.

Conclude with `h2 (Finset.mem_sdiff.mpr ⟨hT.mem_toFinset.mpr h3, h1⟩)`. Establish `hTSg : ∀ v ∈ T, v ∉ Sg` using `fun v hv => (Finset.mem_sdiff.mp hv).2`. Establish `hPi : ∀ g, (∏ᶠ (v : I) (_ : v ∉ Sg), if v ∈ S g then b v else a v) = ∏ v ∈ T ∪ S g, if v ∈ S g then b v else a v`. Introduce `g`. Apply `finprod_cond_eq_prod_of_cond_iff` to reduce the goal to its premises.

Introduce `v hv`. Prove the components needed by the constructor for the conclusion. Introduce `hvS`. Distinguish the cases in `hs : v ∈ S g`. Conclude with `Finset.mem_union_right _ hs`.

Rewrite `hv` using `[if_neg hs]`. Use `Finset.mem_union_left _ ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hvT`. Conclude with `hv (hout v hvS hvT).1`. Introduce `hvU`.

Break down `Finset.mem_union.mp hvU with h | h` into its components or cases. Conclude with `hTSg v h`. Conclude with `hSg g v h`. Establish `hPi_zero : ∀ g, ¬ S g ⊆ T → (∏ᶠ (v : I) (_ : v ∉ Sg), if v ∈ S g then b v else a v) = 0`. Introduce `g hsub`.

Rewrite using `[hPi g]`. Take `⟨v, hvS, hvT⟩` from `Finset.not_subset.mp hsub`. Apply `Finset.prod_eq_zero (Finset.mem_union_right _ hvS)` to reduce the goal to its premises. Rewrite using `[if_pos hvS]`. Conclude with `(hout v (hSg g v hvS) hvT).2`.

Establish `hPi_w : ∀ g, S g ⊆ T → (∏ᶠ (v : I) (_ : v ∉ Sg), if v ∈ S g then b v else a v) = ∏ v ∈ T, if v ∈ S g then b v else a v`. Introduce `g hsub`. Rewrite using `[hPi g, Finset.union_eq_left.mpr hsub]`. Establish `hw : ∀ s ⊆ T, (∏ v ∈ T, if v ∈ s then b v else a v) = (∏ v ∈ s, b v) * ∏ v ∈ T \ s, a v`. Introduce `s hs`.

Rewrite using `[← Finset.prod_sdiff hs, mul_comm]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun v hv => if_pos hv`. Conclude with `Finset.prod_congr rfl fun v hv => if_neg (Finset.mem_sdiff.mp hv).2`. Establish `hw0 : ∀ s ⊆ T, (∃ v ∈ s, ¬ E v) → (∏ v ∈ T, if v ∈ s then b v else a v) = 0`.

Introduce and unpack `s hs ⟨v, hv, hE⟩`. Rewrite using `[hw s hs, Finset.prod_eq_zero hv (hb v hE), zero_mul]`. Establish `hA : {g | P g ∧ (∏ᶠ (v : I) (_ : v ∉ Sg), if v ∈ S g then b v else a v) ≠ 0}.Finite`. Apply `Set.Finite.of_finite_image (f := S)` to reduce the goal to its premises. Apply `(T.powerset.finite_toSet).subset` to reduce the goal to its premises.

Introduce and unpack `_ ⟨g, ⟨_, hne⟩, rfl⟩`. Rewrite using `[Finset.mem_coe, Finset.mem_powerset]`. Assume the negation of the conclusion as `hsub`. Conclude with `hne (hPi_zero g hsub)`. Introduce `g hg g' hg' h`.

Conclude with `inj g g' hg.1 hg'.1 h`. Use `⟨hA, ?_⟩` and prove the remaining obligations. Establish `hsupp : Function.support (fun g => one (P g) * (∏ᶠ (v : I) (_ : v ∉ Sg), if v ∈ S g then b v else a v)) ⊆ ↑hA.toFinset`. Introduce `g hg`. Rewrite using `[Set.Finite.coe_toFinset]`.

Simplify using `only [Function.mem_support] at hg`. Distinguish the cases in `hP : P g`. Use `⟨hP, fun h0 => hg ?_⟩` and prove the remaining obligations. Rewrite using `[h0, mul_zero]`. Conclude with `absurd (by simp [one, hP]) hg`.

Rewrite using `[finsum_eq_sum_of_support_subset _ hsupp]`. Establish `hmemA : ∀ g ∈ hA.toFinset, P g ∧ S g ⊆ T ∧ (∏ v ∈ T, if v ∈ S g then b v else a v) ≠ 0`. Introduce `g hg`. Rewrite `hg` using `[Set.Finite.mem_toFinset]`. Establish `hsub : S g ⊆ T`.

Assume the negation of the conclusion as `h`. Conclude with `hg.2 (hPi_zero g h)`. Conclude with `⟨hg.1, hsub, by rw [← hPi_w g hsub]; exact hg.2⟩`. Rewrite using `[Finset.sum_congr rfl (g := fun g => ∏ v ∈ T, if v ∈ S g then b v else a v) (fun g hg => by`. Rewrite using `[hPi_w g (hmemA g hg).2.1]`.

Simplify using `[one, (hmemA g hg).1])]`. Rewrite using `[← Finset.sum_image (g := S) (f := fun s => ∏ v ∈ T, if v ∈ s then b v else a v) (fun g hg g' hg' h => inj g g' (hmemA g hg).1 (hmemA g' hg').1 h)]`. Use `set B := T.powerset.filter (fun s => Even s.card ∧ ∀ v ∈ s, E v) with hB`. Establish `hsubB : hA.toFinset.image S ⊆ B`. Introduce `s hs`.

Take `⟨g, hg, rfl⟩` from `Finset.mem_image.mp hs`. Take `⟨hP, hsub, hne⟩` from `hmemA g hg`. Rewrite using `[hB, Finset.mem_filter, Finset.mem_powerset]`. Use `⟨hsub, ev g hP, fun v hv => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hE`.

Conclude with `hne (hw0 _ hsub ⟨v, hv, hE⟩)`. Rewrite using `[Finset.sum_subset hsubB (fun s hsB hsI => by`. Rewrite `hsB` using `[hB, Finset.mem_filter, Finset.mem_powerset]`. Assume the negation of the conclusion as `hne`. Take `⟨g, hP, rfl⟩` from `surj s hsB.2.1 hsB.2.2`.

Apply `hsI` to reduce the goal to its premises. Use `Finset.mem_image.mpr ⟨g, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `⟨hP, by rw [hPi_w g hsB.1]; exact hne⟩)]`. Establish `hR : ∀ f : I → ℂ, (∀ v, a v = 1 → b v = 0 → f v = 1) → (∏ᶠ (v : I) (_ : v ∉ Sg), f v) = ∏ v ∈ T, f v`.

Introduce `f hf`. Apply `finprod_cond_eq_prod_of_cond_iff` to reduce the goal to its premises. Introduce `v hv`. Prove the components needed by the constructor for the conclusion. Introduce `hvS`.

Assume the negation of the conclusion as `hvT`. Conclude with `hv (hf v (hout v hvS hvT).1 (hout v hvS hvT).2)`. Conclude with `hTSg v`. Establish `r1 : (∏ᶠ (v : I) (_ : v ∉ Sg), (a v + b v)) = ∏ v ∈ T, (a v + b v)` using `hR _ (fun v h1 h2 => by simp [h1, h2])`. Establish `r2 : (∏ᶠ (v : I) (_ : v ∉ Sg), (a v - b v)) = ∏ v ∈ T, (a v - b v)` using `hR _ (fun v h1 h2 => by simp [h1, h2])`.

Establish `e1 : ∏ v ∈ T, (a v + b v) = ∑ t ∈ T.powerset, (∏ v ∈ t, b v) * ∏ v ∈ T \ t, a v`. Rewrite using `[← Finset.prod_add]`. Conclude with `Finset.prod_congr rfl fun v _ => add_comm _ _`. Establish `e2 : ∏ v ∈ T, (a v - b v) = ∑ t ∈ T.powerset, (-1) ^ t.card * ((∏ v ∈ t, b v) * ∏ v ∈ T \ t, a v)`. Establish `h' : ∏ v ∈ T, (a v - b v) = ∏ v ∈ T, (-b v + a v)` using `Finset.prod_congr rfl fun v _ => by ring`.

Rewrite using `[h', Finset.prod_add]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_neg]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[r1, r2, e1, e2, hB, Finset.sum_filter, ← Finset.sum_add_distrib, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun t ht => ?_` and prove the remaining obligations. Rewrite `ht` using `[Finset.mem_powerset]`. Rewrite using `[← hw t ht]`. Distinguish the cases in `hev : Even t.card`. Rewrite using `[hev.neg_one_pow]`.

Distinguish the cases in `hE : ∀ v ∈ t, E v`. Rewrite using `[if_pos ⟨hev, hE⟩]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hE` using `[if_neg (fun h => hE h.2)] push_neg`. Rewrite using `[hw0 t ht hE]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (fun h => hev h.1), (Nat.not_even_iff_odd.mp hev).neg_one_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem abs_sum {I G : Type} (Sg : Finset I) (P : G → Prop) (S : G → Finset I) (E : I → Prop) (a b : I → ℂ)
    (hab : ∀ᶠ v in Filter.cofinite, a v = 1 ∧ b v = 0) (hb : ∀ v, ¬ E v → b v = 0)
    (inj : ∀ g g', P g → P g' → S g = S g' → g = g') (hSg : ∀ g, ∀ v ∈ S g, v ∉ Sg)
    (ev : ∀ g, P g → Even (S g).card)
    (surj : ∀ s : Finset I, Even s.card → (∀ v ∈ s, E v) → ∃ g, P g ∧ S g = s) :
    {g | P g ∧ (∏ᶠ (v : I) (_ : v ∉ Sg), if v ∈ S g then b v else a v) ≠ 0}.Finite ∧
    ∑ᶠ g, one (P g) * (∏ᶠ (v : I) (_ : v ∉ Sg), if v ∈ S g then b v else a v) =
      1 / 2 * ((∏ᶠ (v : I) (_ : v ∉ Sg), (a v + b v)) + ∏ᶠ (v : I) (_ : v ∉ Sg), (a v - b v)) := by
  classical
  have hT : {v | ¬(a v = 1 ∧ b v = 0)}.Finite := Filter.eventually_cofinite.mp hab
  set T : Finset I := hT.toFinset \ Sg with hTdef
  have hout : ∀ v, v ∉ Sg → v ∉ T → a v = 1 ∧ b v = 0 := by
    intro v h1 h2
    by_contra h3
    exact h2 (Finset.mem_sdiff.mpr ⟨hT.mem_toFinset.mpr h3, h1⟩)
  have hTSg : ∀ v ∈ T, v ∉ Sg := fun v hv => (Finset.mem_sdiff.mp hv).2
  have hPi : ∀ g, (∏ᶠ (v : I) (_ : v ∉ Sg), if v ∈ S g then b v else a v) =
      ∏ v ∈ T ∪ S g, if v ∈ S g then b v else a v := by
    intro g
    apply finprod_cond_eq_prod_of_cond_iff
    intro v hv
    constructor
    · intro hvS
      by_cases hs : v ∈ S g
      · exact Finset.mem_union_right _ hs
      · rw [if_neg hs] at hv
        refine Finset.mem_union_left _ ?_
        by_contra hvT
        exact hv (hout v hvS hvT).1
    · intro hvU
      rcases Finset.mem_union.mp hvU with h | h
      · exact hTSg v h
      · exact hSg g v h
  have hPi_zero : ∀ g, ¬ S g ⊆ T →
      (∏ᶠ (v : I) (_ : v ∉ Sg), if v ∈ S g then b v else a v) = 0 := by
    intro g hsub
    rw [hPi g]
    obtain ⟨v, hvS, hvT⟩ := Finset.not_subset.mp hsub
    apply Finset.prod_eq_zero (Finset.mem_union_right _ hvS)
    rw [if_pos hvS]
    exact (hout v (hSg g v hvS) hvT).2
  have hPi_w : ∀ g, S g ⊆ T →
      (∏ᶠ (v : I) (_ : v ∉ Sg), if v ∈ S g then b v else a v) =
        ∏ v ∈ T, if v ∈ S g then b v else a v := by
    intro g hsub
    rw [hPi g, Finset.union_eq_left.mpr hsub]
  have hw : ∀ s ⊆ T, (∏ v ∈ T, if v ∈ s then b v else a v) =
      (∏ v ∈ s, b v) * ∏ v ∈ T \ s, a v := by
    intro s hs
    rw [← Finset.prod_sdiff hs, mul_comm]
    congr 1
    · exact Finset.prod_congr rfl fun v hv => if_pos hv
    · exact Finset.prod_congr rfl fun v hv => if_neg (Finset.mem_sdiff.mp hv).2
  have hw0 : ∀ s ⊆ T, (∃ v ∈ s, ¬ E v) → (∏ v ∈ T, if v ∈ s then b v else a v) = 0 := by
    rintro s hs ⟨v, hv, hE⟩
    rw [hw s hs, Finset.prod_eq_zero hv (hb v hE), zero_mul]
  have hA : {g | P g ∧ (∏ᶠ (v : I) (_ : v ∉ Sg), if v ∈ S g then b v else a v) ≠ 0}.Finite := by
    apply Set.Finite.of_finite_image (f := S)
    · apply (T.powerset.finite_toSet).subset
      rintro _ ⟨g, ⟨_, hne⟩, rfl⟩
      rw [Finset.mem_coe, Finset.mem_powerset]
      by_contra hsub
      exact hne (hPi_zero g hsub)
    · intro g hg g' hg' h
      exact inj g g' hg.1 hg'.1 h
  refine ⟨hA, ?_⟩
  have hsupp : Function.support (fun g => one (P g) *
      (∏ᶠ (v : I) (_ : v ∉ Sg), if v ∈ S g then b v else a v)) ⊆ ↑hA.toFinset := by
    intro g hg
    rw [Set.Finite.coe_toFinset]
    simp only [Function.mem_support] at hg
    by_cases hP : P g
    · refine ⟨hP, fun h0 => hg ?_⟩
      rw [h0, mul_zero]
    · exact absurd (by simp [one, hP]) hg
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hmemA : ∀ g ∈ hA.toFinset, P g ∧ S g ⊆ T ∧
      (∏ v ∈ T, if v ∈ S g then b v else a v) ≠ 0 := by
    intro g hg
    rw [Set.Finite.mem_toFinset] at hg
    have hsub : S g ⊆ T := by
      by_contra h
      exact hg.2 (hPi_zero g h)
    exact ⟨hg.1, hsub, by rw [← hPi_w g hsub]; exact hg.2⟩
  rw [Finset.sum_congr rfl (g := fun g => ∏ v ∈ T, if v ∈ S g then b v else a v) (fun g hg => by
    rw [hPi_w g (hmemA g hg).2.1]
    simp [one, (hmemA g hg).1])]
  rw [← Finset.sum_image (g := S) (f := fun s => ∏ v ∈ T, if v ∈ s then b v else a v)
    (fun g hg g' hg' h => inj g g' (hmemA g hg).1 (hmemA g' hg').1 h)]
  set B := T.powerset.filter (fun s => Even s.card ∧ ∀ v ∈ s, E v) with hB
  have hsubB : hA.toFinset.image S ⊆ B := by
    intro s hs
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hP, hsub, hne⟩ := hmemA g hg
    rw [hB, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hsub, ev g hP, fun v hv => ?_⟩
    by_contra hE
    exact hne (hw0 _ hsub ⟨v, hv, hE⟩)
  rw [Finset.sum_subset hsubB (fun s hsB hsI => by
    rw [hB, Finset.mem_filter, Finset.mem_powerset] at hsB
    by_contra hne
    obtain ⟨g, hP, rfl⟩ := surj s hsB.2.1 hsB.2.2
    apply hsI
    refine Finset.mem_image.mpr ⟨g, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨hP, by rw [hPi_w g hsB.1]; exact hne⟩)]
  have hR : ∀ f : I → ℂ, (∀ v, a v = 1 → b v = 0 → f v = 1) →
      (∏ᶠ (v : I) (_ : v ∉ Sg), f v) = ∏ v ∈ T, f v := by
    intro f hf
    apply finprod_cond_eq_prod_of_cond_iff
    intro v hv
    constructor
    · intro hvS
      by_contra hvT
      exact hv (hf v (hout v hvS hvT).1 (hout v hvS hvT).2)
    · exact hTSg v
  have r1 : (∏ᶠ (v : I) (_ : v ∉ Sg), (a v + b v)) = ∏ v ∈ T, (a v + b v) :=
    hR _ (fun v h1 h2 => by simp [h1, h2])
  have r2 : (∏ᶠ (v : I) (_ : v ∉ Sg), (a v - b v)) = ∏ v ∈ T, (a v - b v) :=
    hR _ (fun v h1 h2 => by simp [h1, h2])
  have e1 : ∏ v ∈ T, (a v + b v) = ∑ t ∈ T.powerset, (∏ v ∈ t, b v) * ∏ v ∈ T \ t, a v := by
    rw [← Finset.prod_add]
    exact Finset.prod_congr rfl fun v _ => add_comm _ _
  have e2 : ∏ v ∈ T, (a v - b v) =
      ∑ t ∈ T.powerset, (-1) ^ t.card * ((∏ v ∈ t, b v) * ∏ v ∈ T \ t, a v) := by
    have h' : ∏ v ∈ T, (a v - b v) = ∏ v ∈ T, (-b v + a v) :=
      Finset.prod_congr rfl fun v _ => by ring
    rw [h', Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_neg]
    ring
  rw [r1, r2, e1, e2, hB, Finset.sum_filter, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_powerset] at ht
  rw [← hw t ht]
  by_cases hev : Even t.card
  · rw [hev.neg_one_pow]
    by_cases hE : ∀ v ∈ t, E v
    · rw [if_pos ⟨hev, hE⟩]
      ring
    · rw [if_neg (fun h => hE h.2)]
      push_neg at hE
      rw [hw0 t ht hE]
      ring
  · rw [if_neg (fun h => hev h.1), (Nat.not_even_iff_odd.mp hev).neg_one_pow]
    ring

open Classical in
/- English proof (translation)
Establish `h1 : h 1 = 1` using `(hN 1).mp (one_mem N)`. Establish `hval : ∀ t, h t ≠ 1 → h t = -1` using `fun t ht => (hv t).resolve_left ht`. Establish `key : ∀ q : Γ ⧸ N, h q.out = 1 ↔ q = ((1 : Γ) : Γ ⧸ N)`. Introduce `q`. Use `conv_rhs => rw [← QuotientGroup.out_eq' q]`.

Rewrite using `[QuotientGroup.eq, mul_one, inv_mem_iff, hN]`. Repeatedly rewrite using `[key]`. Use `split_ifs with hy`. Take `⟨y, hy⟩` from `hy`. Establish `hyq : ((y : Γ ⧸ N)) ≠ ((1 : Γ) : Γ ⧸ N)`.

Introduce `e`. Rewrite `e` using `[QuotientGroup.eq, mul_one, inv_mem_iff, hN]`. Conclude with `hy e`. Establish `hy' : h y = -1` using `hval y hy`. Establish `hsub : Function.support (fun q : Γ ⧸ N => if q = ((1 : Γ) : Γ ⧸ N) then α else β) ⊆ ↑({((1 : Γ) : Γ ⧸ N), (y : Γ ⧸ N)} : Finset (Γ ⧸ N))`.

Introduce `q _`. Distinguish the cases in `hq1 : q = ((1 : Γ) : Γ ⧸ N)`. Simplify using `[hq1]`. Establish `hqo : h q.out = -1` using `hval _ (fun e => hq1 ((key q).mp e))`. Establish `hinv : h (q.out)⁻¹ = -1`.

Establish `e` using `hm q.out (q.out)⁻¹`. Rewrite `e` using `[mul_inv_cancel, h1, hqo]`. Take the linear combination `e`. Establish `hqy : q = (y : Γ ⧸ N)` using `by conv_lhs => rw [← QuotientGroup.out_eq' q]`. Rewrite using `[QuotientGroup.eq, hN, hm, hinv, hy']`.

Evaluate the numerical expressions. Simplify using `[hqy]`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsub, Finset.sum_pair (Ne.symm hyq), if_pos rfl, if_neg hyq]`. Use `push_neg at hy`. Rewrite using `[add_zero]`.

Establish `hall : ∀ q : Γ ⧸ N, q = ((1 : Γ) : Γ ⧸ N)` using `fun q => (key q).mp (hy _)`. Rewrite using `[finsum_eq_single _ ((1 : Γ) : Γ ⧸ N) (fun q hq => absurd (hall q) hq), if_pos rfl]`.
-/
private theorem two_cls {Γ : Type} [Group Γ] (N : Subgroup Γ) (h : Γ → ℂ) (hv : ∀ t, h t = 1 ∨ h t = -1)
    (hN : ∀ t, t ∈ N ↔ h t = 1) (hm : ∀ x y, h (x * y) = h x * h y) (α β : ℂ) :
    ∑ᶠ q : Γ ⧸ N, (if h q.out = 1 then α else β) = α + if ∃ y, h y ≠ 1 then β else 0 := by
  have h1 : h 1 = 1 := (hN 1).mp (one_mem N)
  have hval : ∀ t, h t ≠ 1 → h t = -1 := fun t ht => (hv t).resolve_left ht
  have key : ∀ q : Γ ⧸ N, h q.out = 1 ↔ q = ((1 : Γ) : Γ ⧸ N) := by
    intro q
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [QuotientGroup.eq, mul_one, inv_mem_iff, hN]
  simp_rw [key]
  split_ifs with hy
  · obtain ⟨y, hy⟩ := hy
    have hyq : ((y : Γ ⧸ N)) ≠ ((1 : Γ) : Γ ⧸ N) := by
      intro e
      rw [QuotientGroup.eq, mul_one, inv_mem_iff, hN] at e
      exact hy e
    have hy' : h y = -1 := hval y hy
    have hsub : Function.support (fun q : Γ ⧸ N => if q = ((1 : Γ) : Γ ⧸ N) then α else β) ⊆
        ↑({((1 : Γ) : Γ ⧸ N), (y : Γ ⧸ N)} : Finset (Γ ⧸ N)) := by
      intro q _
      by_cases hq1 : q = ((1 : Γ) : Γ ⧸ N)
      · simp [hq1]
      · have hqo : h q.out = -1 := hval _ (fun e => hq1 ((key q).mp e))
        have hinv : h (q.out)⁻¹ = -1 := by
          have e := hm q.out (q.out)⁻¹
          rw [mul_inv_cancel, h1, hqo] at e
          linear_combination e
        have hqy : q = (y : Γ ⧸ N) := by
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rw [QuotientGroup.eq, hN, hm, hinv, hy']
          norm_num
        simp [hqy]
    rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_pair (Ne.symm hyq), if_pos rfl, if_neg hyq]
  · push_neg at hy
    rw [add_zero]
    have hall : ∀ q : Γ ⧸ N, q = ((1 : Γ) : Γ ⧸ N) := fun q => (key q).mp (hy _)
    rw [finsum_eq_single _ ((1 : Γ) : Γ ⧸ N) (fun q hq => absurd (hall q) hq), if_pos rfl]

open Loc

/- English proof (translation)
Unfold `hs`. Use `split_ifs`. Use `left`. Both sides reduce to the same expression. Use `right`.

Both sides reduce to the same expression.
-/
private theorem hs_cases {K : Type} [Field K] (D x : K) : hs D x = 1 ∨ hs D x = -1 := by
  unfold hs
  split_ifs
  · left
    rfl
  · right
    rfl

/- English proof (translation)
Unfold `hs`. Use `split_ifs with h`. Conclude with `⟨fun _ => h, fun _ => rfl⟩`. Use `⟨fun h1 => ?_, fun h1 => absurd h1 h⟩` and prove the remaining obligations. Evaluate the numerical expressions using `at h1`.
-/
private theorem hs_iff {K : Type} [Field K] (D x : K) : hs D x = 1 ↔ ∃ a b : K, a ^ 2 - D * b ^ 2 = x := by
  unfold hs
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · refine ⟨fun h1 => ?_, fun h1 => absurd h1 h⟩
    norm_num at h1

/- English proof (translation)
Establish `h2 : (2 : K) ≠ 0` using `two_ne_zero`. Rewrite using `[hs_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Use `⟨(z : QuadraticAlgebra K (-1) τ).re + τ * (z : QuadraticAlgebra K (-1) τ).im / 2, (z : QuadraticAlgebra K (-1) τ).im / 2, ?_⟩` and prove the remaining obligations.

Simplify using `only [Units.coe_map, MonoidHom.coe_coe, QuadraticAlgebra.norm_def]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨a, b, hab⟩`. Establish `hz : IsUnit (⟨a - τ * b, 2 * b⟩ : QuadraticAlgebra K (-1) τ)`.

Rewrite using `[QuadraticAlgebra.isUnit_iff_norm_isUnit, QuadraticAlgebra.norm_def, isUnit_iff_ne_zero]`. Establish `e : (a - τ * b) * (a - τ * b) + τ * (a - τ * b) * (2 * b) - (-1) * (2 * b) * (2 * b) = (t : K)`. Rewrite using `[← hab]`. Expand and normalize the polynomial expressions, which then agree. Simplify `t.ne_zero` using `only [e]`.

Use `⟨hz.unit, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `only [Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_spec, QuadraticAlgebra.norm_def]`. Rewrite using `[← hab]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem mem_NE {K : Type} [Field K] [CharZero K] (τ : K) (t : Kˣ) : t ∈ NE τ ↔ hs (τ ^ 2 - 4) (t : K) = 1 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  rw [hs_iff]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(z : QuadraticAlgebra K (-1) τ).re + τ * (z : QuadraticAlgebra K (-1) τ).im / 2,
      (z : QuadraticAlgebra K (-1) τ).im / 2, ?_⟩
    simp only [Units.coe_map, MonoidHom.coe_coe, QuadraticAlgebra.norm_def]
    field_simp
    ring
  · rintro ⟨a, b, hab⟩
    have hz : IsUnit (⟨a - τ * b, 2 * b⟩ : QuadraticAlgebra K (-1) τ) := by
      rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, QuadraticAlgebra.norm_def, isUnit_iff_ne_zero]
      have e : (a - τ * b) * (a - τ * b) + τ * (a - τ * b) * (2 * b) - (-1) * (2 * b) * (2 * b) = (t : K) := by
        rw [← hab]
        ring
      simpa only [e] using t.ne_zero
    refine ⟨hz.unit, ?_⟩
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_spec, QuadraticAlgebra.norm_def]
    rw [← hab]
    ring

/- English proof (translation)
Take `⟨s, rfl⟩` from `h`. Establish `hs0 : s ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h0`. Establish `h2 : (2 : K) ≠ 0` using `two_ne_zero`.

Rewrite using `[hs_iff]`. Use `⟨(x + 1) / 2, (x - 1) / (2 * s), ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hs_sq {K : Type} [Field K] [CharZero K] {D : K} (h0 : D ≠ 0) (h : IsSquare D) (x : K) : hs D x = 1 := by
  obtain ⟨s, rfl⟩ := h
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at h0
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  rw [hs_iff]
  refine ⟨(x + 1) / 2, (x - 1) / (2 * s), ?_⟩
  field_simp
  ring

/- English proof (translation)
Rewrite using `[hs_iff]`. Conclude with `⟨Real.sqrt x, 0, by rw [Real.sq_sqrt h.le]; ring⟩`.
-/
private theorem hs_pos (D : ℝ) {x : ℝ} (h : 0 < x) : hs D x = 1 := by
  rw [hs_iff]
  exact ⟨Real.sqrt x, 0, by rw [Real.sq_sqrt h.le]; ring⟩

/- English proof (translation)
Rewrite `h`, the goal using `[hs_iff]`. Take `⟨a, b, hab⟩` from `h`. Conclude with `⟨f a, f b, by rw [← hab, map_sub, map_mul, map_pow, map_pow]⟩`.
-/
private theorem hs_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') {D x : K} (h : hs D x = 1) : hs (f D) (f x) = 1 := by
  rw [hs_iff] at h ⊢
  obtain ⟨a, b, hab⟩ := h
  exact ⟨f a, f b, by rw [← hab, map_sub, map_mul, map_pow, map_pow]⟩

/- English proof (translation)
Rewrite `h` using `[hs_iff]`. Take `⟨a, b, rfl⟩` from `h`. Establish `h0 : 0 ≤ a ^ 2 - D * b ^ 2` using `by nlinarith [sq_nonneg a, sq_nonneg b]`. Conclude with `lt_of_le_of_ne h0 (Ne.symm hx)`.
-/
private theorem pos_of_hs {D x : ℝ} (hD : D < 0) (hx : x ≠ 0) (h : hs D x = 1) : 0 < x := by
  rw [hs_iff] at h
  obtain ⟨a, b, rfl⟩ := h
  have h0 : 0 ≤ a ^ 2 - D * b ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg b]
  exact lt_of_le_of_ne h0 (Ne.symm hx)

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [elmap, lmap]`.
-/
private theorem elmap_smul {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ τ : K} (t : K) (m : EL Δ τ) :
    elmap f (t • m) = f t • elmap f m := by
  ext <;> simp [elmap, lmap]

open Classical in
/- English proof (translation)
Use `set D := τ ^ 2 - 4 with hD`. Establish `hv : ∀ t : Kˣ, hs D (t : K) = 1 ∨ hs D (t : K) = -1` using `fun t => hs_cases D t`. Establish `hN : ∀ t : Kˣ, t ∈ NE τ ↔ hs D (t : K) = 1` using `fun t => mem_NE τ t`. Establish `h1 : hs D ((1 : Kˣ) : K) = 1` using `(hN 1).mp (one_mem _)`. Establish `hinv : ∀ x : Kˣ, hs D (x : K) ≠ 1 → hs D ((x⁻¹ : Kˣ) : K) = -1`.

Introduce `x hx`. Establish `e` using `hm x x⁻¹`. Rewrite `e` using `[mul_inv_cancel, h1, (hv x).resolve_left hx]`. Take the linear combination `e`. Establish `part1 : ∀ t : Kˣ, f t = if hs D (t : K) = 1 then f 1 else b`.

Introduce `t`. Use `split_ifs with ht`. Establish `e` using `hf t ((hN t).mpr ht) 1`. Rewrite `e` using `[mul_one]`. Then use the resulting hypothesis. Establish `hex : ∃ y : Kˣ, hs D (y : K) ≠ 1` using `⟨t, ht⟩`.

Rewrite using `[hb, dif_pos hex]`. Establish `hc : hs D ((hex.choose : Kˣ) : K) ≠ 1` using `hex.choose_spec`. Establish `hmem : t * hex.choose⁻¹ ∈ NE τ`. Rewrite using `[hN, hm, (hv t).resolve_left ht, hinv _ hc]`. Evaluate the numerical expressions.

Establish `e` using `hf (t * hex.choose⁻¹) hmem hex.choose`. Rewrite `e` using `[inv_mul_cancel_right]`. Then use the resulting hypothesis. Establish `T1` using `two_cls (NE τ) (fun t : Kˣ => hs D (t : K)) hv hN hm (f 1) b`. Establish `T2` using `two_cls (NE τ) (fun t : Kˣ => hs D (t : K)) hv hN hm (f 1) (-b)`. Use `beta_reduce at T1 T2`.

Use `⟨part1, ?_, ?_⟩` and prove the remaining obligations. Establish `e : ∀ q : Kˣ ⧸ NE τ, f q.out = if hs D ((q.out : Kˣ) : K) = 1 then f 1 else b` using `fun q => part1 _`. Rewrite using `[finsum_congr e, T1]`. Use `split_ifs with hex`. Both sides reduce to the same expression.

Rewrite using `[hb, dif_neg hex, add_zero]`. Establish `e : ∀ q : Kˣ ⧸ NE τ, hs D ((q.out : Kˣ) : K) * f q.out = if hs D ((q.out : Kˣ) : K) = 1 then f 1 else -b`. Introduce `q`. Rewrite using `[part1 q.out]`. Use `split_ifs with hq`.

Rewrite using `[hq, one_mul]`. Rewrite using `[(hv _).resolve_left hq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[finsum_congr e, T2]`. Use `split_ifs with hex`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hb, dif_neg hex]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem loc_two {K : Type} [Field K] [CharZero K] (τ : K)
    (hm : ∀ x y : Kˣ, hs (τ ^ 2 - 4) ((x * y : Kˣ) : K) = hs (τ ^ 2 - 4) (x : K) * hs (τ ^ 2 - 4) (y : K))
    (f : Kˣ → ℂ) (hf : ∀ t ∈ NE τ, ∀ x, f (t * x) = f x) (b : ℂ)
    (hb : b = if h : ∃ y : Kˣ, hs (τ ^ 2 - 4) (y : K) ≠ 1 then f h.choose else 0) :
    (∀ t : Kˣ, f t = if hs (τ ^ 2 - 4) (t : K) = 1 then f 1 else b) ∧
    (∑ᶠ q : Kˣ ⧸ NE τ, f q.out = f 1 + b) ∧
    (∑ᶠ q : Kˣ ⧸ NE τ, hs (τ ^ 2 - 4) ((q.out : Kˣ) : K) * f q.out = f 1 - b) := by
  set D := τ ^ 2 - 4 with hD
  have hv : ∀ t : Kˣ, hs D (t : K) = 1 ∨ hs D (t : K) = -1 := fun t => hs_cases D t
  have hN : ∀ t : Kˣ, t ∈ NE τ ↔ hs D (t : K) = 1 := fun t => mem_NE τ t
  have h1 : hs D ((1 : Kˣ) : K) = 1 := (hN 1).mp (one_mem _)
  have hinv : ∀ x : Kˣ, hs D (x : K) ≠ 1 → hs D ((x⁻¹ : Kˣ) : K) = -1 := by
    intro x hx
    have e := hm x x⁻¹
    rw [mul_inv_cancel, h1, (hv x).resolve_left hx] at e
    linear_combination e
  have part1 : ∀ t : Kˣ, f t = if hs D (t : K) = 1 then f 1 else b := by
    intro t
    split_ifs with ht
    · have e := hf t ((hN t).mpr ht) 1
      rwa [mul_one] at e
    · have hex : ∃ y : Kˣ, hs D (y : K) ≠ 1 := ⟨t, ht⟩
      rw [hb, dif_pos hex]
      have hc : hs D ((hex.choose : Kˣ) : K) ≠ 1 := hex.choose_spec
      have hmem : t * hex.choose⁻¹ ∈ NE τ := by
        rw [hN, hm, (hv t).resolve_left ht, hinv _ hc]
        norm_num
      have e := hf (t * hex.choose⁻¹) hmem hex.choose
      rwa [inv_mul_cancel_right] at e
  have T1 := two_cls (NE τ) (fun t : Kˣ => hs D (t : K)) hv hN hm (f 1) b
  have T2 := two_cls (NE τ) (fun t : Kˣ => hs D (t : K)) hv hN hm (f 1) (-b)
  beta_reduce at T1 T2
  refine ⟨part1, ?_, ?_⟩
  · have e : ∀ q : Kˣ ⧸ NE τ, f q.out = if hs D ((q.out : Kˣ) : K) = 1 then f 1 else b :=
      fun q => part1 _
    rw [finsum_congr e, T1]
    split_ifs with hex
    · rfl
    · rw [hb, dif_neg hex, add_zero]
  · have e : ∀ q : Kˣ ⧸ NE τ, hs D ((q.out : Kˣ) : K) * f q.out =
        if hs D ((q.out : Kˣ) : K) = 1 then f 1 else -b := by
      intro q
      rw [part1 q.out]
      split_ifs with hq
      · rw [hq, one_mul]
      · rw [(hv _).resolve_left hq]
        ring
    rw [finsum_congr e, T2]
    split_ifs with hex
    · ring
    · rw [hb, dif_neg hex]
      ring

open Classical in
/- English proof (translation)
Establish `hs : Function.mulSupport u ⊆ ↑s`. Introduce `v hv`. Assume the negation of the conclusion as `hvs`. Establish `hvs' : v ∉ s` using `fun h' => hvs (Finset.mem_coe.mpr h')`. Conclude with `hv (by rw [h v, if_neg hvs'])`.

Rewrite using `[finprod_eq_prod_of_mulSupport_subset u hs, Finset.prod_congr rfl (g := fun _ => (-1 : ℂ)) (fun v hv => by rw [h v, if_pos hv]), Finset.prod_const]`.
-/
private theorem finprod_sign {I : Type} (u : I → ℂ) (s : Finset I) (h : ∀ v, u v = if v ∈ s then -1 else 1) :
    ∏ᶠ v, u v = (-1) ^ s.card := by
  have hs : Function.mulSupport u ⊆ ↑s := by
    intro v hv
    by_contra hvs
    have hvs' : v ∉ s := fun h' => hvs (Finset.mem_coe.mpr h')
    exact hv (by rw [h v, if_neg hvs'])
  rw [finprod_eq_prod_of_mulSupport_subset u hs,
    Finset.prod_congr rfl (g := fun _ => (-1 : ℂ)) (fun v hv => by rw [h v, if_pos hv]), Finset.prod_const]

open Classical in
/- English proof (translation)
Introduce `F _ _ Δ D hOk τ c d m hCM hSpl hDat`. Establish `hD0 : τ ^ 2 - 4 ≠ 0` using `hDat.reg`. Establish `hDv : ∀ v : Pl F, cv v (τ ^ 2 - 4) = cv v τ ^ 2 - 4` using `fun v => by`. Rewrite using `[map_sub, map_pow, map_ofNat]`. Establish `hCZ : ∀ v : Pl F, CharZero (Kv v)` using `fun v => charZero_of_injective_algebraMap (algebraMap F (Kv v)).injective`.

Establish `hKne : ∀ v : Pl F, cv v (τ ^ 2 - 4) ≠ 0` using `fun v => (map_ne_zero _).mpr hD0`. Take `⟨f, hfdef⟩ : ∃ f : (v : Pl F) → (Kv v)ˣ → ℂ, ∀ v t, f v t = lcount (Ov v) (cv v c) (elmap (cv v) d) ((t : Kv v) • elmap (cv v) m)` from `⟨_, fun _ _ => rfl⟩`. Take `⟨b, hbdef⟩ : ∃ b : Pl F → ℂ, ∀ v, b v = if h : ∃ y : (Kv v)ˣ, hs (cv v τ ^ 2 - 4) (y : Kv v) ≠ 1 then f v h.choose else 0` from `⟨_, fun _ => rfl⟩`. Establish `hmulK : ∀ v : Pl F, ∀ x y : (Kv v)ˣ, hs (cv v τ ^ 2 - 4) ((x * y : (Kv v)ˣ) : Kv v) = hs (cv v τ ^ 2 - 4) (x : Kv v) * hs (cv v τ ^ 2 - 4) (y : Kv v)`. Introduce `v x y`.

Rewrite using `[Units.val_mul]`. Conclude with `hsMul F v _ _ _ (by rw [← hDv]; exact hKne v) x.ne_zero y.ne_zero`. Establish `loc : ∀ v, v ∉ D.Sg → (∀ t : (Kv v)ˣ, f v t = if hs (cv v τ ^ 2 - 4) (t : Kv v) = 1 then f v 1 else b v) ∧ stabSum (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m) = f v 1 + b v ∧ kapSum (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m) = f v 1 - b v`. Introduce `v hv`. Use `haveI := hCZ v`.

Establish `hDatv` using `(modelMap F (Kv v) (cv v) Δ τ c d m hDat).1`. Establish `hinv : ∀ t ∈ NE (cv v τ), ∀ x : (Kv v)ˣ, f v (t * x) = f v x`. Introduce `t ht x`. Rewrite using `[hfdef, hfdef, Units.val_mul, mul_smul]`. Conclude with `lcountNorm (Ov v) (Kv v) _ _ (hOk.off v hv) _ _ _ (datSmul (Kv v) _ _ _ _ _ hDatv x) t ht`.

Take `⟨p1, p2, p3⟩` from `loc_two (cv v τ) (hmulK v) (f v) hinv (b v) (hbdef v)`. Use `⟨p1, ?_, ?_⟩` and prove the remaining obligations. Unfold `stabSum`. Rewrite using `[← p2]`. Conclude with `finsum_congr fun q => (hfdef v _).symm`.

Unfold `kapSum`. Rewrite using `[← p3]`. Conclude with `finsum_congr fun q => by rw [hfdef]`. Establish `hab : ∀ᶠ v in Filter.cofinite, f v 1 = 1 ∧ b v = 0` using `by filter_upwards [genPl F Δ D hOk τ c d m hDat] with v hv haveI := hCZ v`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hfdef, hv 1]`. Simplify using `[one]`. Rewrite using `[hbdef] split_ifs with hex`. Rewrite using `[hfdef, hv, one, if_neg]`. Rewrite using `[mem_NE]`.

Conclude with `hex.choose_spec`. Both sides reduce to the same expression. Establish `hsplit : ∀ v ∈ D.Sg, ∀ z : Kv v, hs (cv v (τ ^ 2 - 4)) z = 1`. Introduce `v hv z`. Use `haveI := hCZ v`.

Conclude with `hs_sq (hKne v) (by rw [hDv]; exact hSpl v hv) z`. Establish `hmulF : ∀ v (x y : Fˣ), hs (cv v (τ ^ 2 - 4)) (cv v ((x * y : Fˣ) : F)) = hs (cv v (τ ^ 2 - 4)) (cv v (x : F)) * hs (cv v (τ ^ 2 - 4)) (cv v (y : F))`. Introduce `v x y`. Rewrite using `[Units.val_mul, map_mul]`. Conclude with `hsMul F v _ _ _ (hKne v) ((map_ne_zero _).mpr x.ne_zero) ((map_ne_zero _).mpr y.ne_zero)`.

Establish `hone : ∀ v, hs (cv v (τ ^ 2 - 4)) (cv v ((1 : Fˣ) : F)) = 1` using `fun v => by`. Rewrite using `[Units.val_one, map_one, hs_iff]`. Conclude with `⟨1, 0, by ring⟩`. Establish `hinvF : ∀ v (x : Fˣ), hs (cv v (τ ^ 2 - 4)) (cv v ((x⁻¹ : Fˣ) : F)) = hs (cv v (τ ^ 2 - 4)) (cv v (x : F))`. Introduce `v x`.

Establish `e` using `hmulF v x x⁻¹`. Rewrite `e` using `[mul_inv_cancel, hone]`. Break down `hs_cases (cv v (τ ^ 2 - 4)) (cv v (x : F)) with h | h` into its components or cases. Rewrite `e`, the goal using `[h]`. Take the linear combination `-e`.

Rewrite `e`, the goal using `[h]`. Take the linear combination `e`. Establish `hrec` using `fun (x : Fˣ) => recip F (τ ^ 2 - 4) (x : F) hD0 x.ne_zero`. Take `⟨S, hS⟩ : ∃ S : Fˣ ⧸ NE τ → Finset (Pl F), ∀ g v, v ∈ S g ↔ hs (cv v (τ ^ 2 - 4)) (cv v ((g.out : Fˣ) : F)) ≠ 1` from `⟨fun g => (hrec g.out).1.toFinset, fun g v => Set.Finite.mem_toFinset _⟩`. Establish `inj : ∀ g g' : Fˣ ⧸ NE τ, TPos ((g.out : Fˣ) : F) → TPos ((g'.out : Fˣ) : F) → S g = S g' → g = g'`.

Introduce `g g' hP hP' hSS`. Rewrite using `[← QuotientGroup.out_eq' g, ← QuotientGroup.out_eq' g', QuotientGroup.eq, mem_NE]`. Apply `hsHasse F (τ ^ 2 - 4) _ hD0 (Units.ne_zero _)` to reduce the goal to its premises. Introduce `σ`. Apply `hs_pos` to reduce the goal to its premises.

Rewrite using `[Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]`. Conclude with `mul_pos (inv_pos.mpr (hP σ)) (hP' σ)`. Introduce `v`. Rewrite using `[hmulF, hinvF]`. Distinguish the cases in `hv : v ∈ D.Sg`.

Simplify using `only [hsplit v hv, mul_one]`. Establish `hiff : hs (cv v (τ ^ 2 - 4)) (cv v ((g.out : Fˣ) : F)) ≠ 1 ↔ hs (cv v (τ ^ 2 - 4)) (cv v ((g'.out : Fˣ) : F)) ≠ 1` using `(hS g v).symm.trans (hSS ▸ hS g' v)`. Apply the tactic sequence `rcases hs_cases (cv v (τ ^ 2 - 4)) (cv v ((g.out : Fˣ) : F)) with h | h <;>`. Break down `hs_cases (cv v (τ ^ 2 - 4)) (cv v ((g'.out : Fˣ) : F)) with h' | h'` into its components or cases. Rewrite using `[h, h']`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `absurd h (hiff.mpr (by rw [h']; norm_num))`. Conclude with `absurd h' (hiff.mp (by rw [h]; norm_num))`. Rewrite using `[h, h']`. Expand and normalize the polynomial expressions, which then agree.

Establish `ev : ∀ g : Fˣ ⧸ NE τ, TPos ((g.out : Fˣ) : F) → Even (S g).card`. Introduce `g hP`. Establish `hr` using `(hrec g.out).2`. Establish `hreal : ∏ σ : F →+* ℝ, hs (σ (τ ^ 2 - 4)) (σ ((g.out : Fˣ) : F)) = 1` using `Finset.prod_eq_one fun σ _ => hs_pos _ (hP σ)`. Establish `hsgn` using `finprod_sign (fun v => hs (cv v (τ ^ 2 - 4)) (cv v ((g.out : Fˣ) : F))) (S g) (by`.

Introduce `v`. Distinguish the cases in `hv : v ∈ S g`. Rewrite using `[if_pos hv]`. Conclude with `(hs_cases _ _).resolve_left ((hS g v).mp hv)`. Rewrite using `[if_neg hv]`.

Assume the negation of the conclusion as `h`. Conclude with `hv ((hS g v).mpr h))`. Rewrite `hr` using `[hsgn, hreal]`. Conclude with `(neg_one_pow_eq_one_iff_even (by norm_num)).mp hr`. Establish `surj : ∀ s : Finset (Pl F), Even s.card → (∀ v ∈ s, ∃ y : (Kv v)ˣ, hs (cv v τ ^ 2 - 4) (y : Kv v) ≠ 1) → ∃ g : Fˣ ⧸ NE τ, TPos ((g.out : Fˣ) : F) ∧ S g = s`.

Introduce `s hs2 hE`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y : (v : Pl F) → (Kv v)ˣ, ∀ v, hs (cv v (τ ^ 2 - 4)) ((y v : (Kv v)ˣ) : Kv v) = if v ∈ s then -1 else 1 := by`. Use `⟨fun v => if h : v ∈ s then (hE v h).choose else 1, fun v => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Distinguish the cases in `hv : v ∈ s`.

Rewrite using `[if_pos hv, dif_pos hv]`. Establish `hc` using `(hE v hv).choose_spec`. Rewrite using `[hDv]`. Conclude with `(hs_cases _ _).resolve_left hc`. Rewrite using `[if_neg hv, dif_neg hv, Units.val_one, hs_iff]`.

Conclude with `⟨1, 0, by ring⟩`. Establish `hfin : {v | hs (cv v (τ ^ 2 - 4)) ((y v : (Kv v)ˣ) : Kv v) ≠ 1}.Finite`. Apply `s.finite_toSet.subset` to reduce the goal to its premises. Introduce `v hv`. Assume the negation of the conclusion as `hvs`.

Apply `hv` to reduce the goal to its premises. Rewrite using `[hy, if_neg (fun h => hvs (Finset.mem_coe.mpr h))]`. Establish `hprod : ∏ᶠ v, hs (cv v (τ ^ 2 - 4)) ((y v : (Kv v)ˣ) : Kv v) = 1`. Rewrite using `[finprod_sign _ s hy]`. Conclude with `hs2.neg_one_pow`.

Take `⟨x, hx0, hxpos, hxloc⟩` from `symbolEx F (τ ^ 2 - 4) hD0 y hfin hprod`. Use `set u := Units.mk0 x hx0 with hu`. Establish `hux : (u : F) = x` using `Units.val_mk0 _`. Use `set n := u⁻¹ * (u : Fˣ ⧸ NE τ).out with hndef`. Establish `hn : n ∈ NE τ` using `QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm`.

Establish `hnF : hs (τ ^ 2 - 4) (n : F) = 1` using `(mem_NE τ n).mp hn`. Establish `hgo : ((u : Fˣ ⧸ NE τ).out : Fˣ) = u * n` using `(mul_inv_cancel_left u _).symm`. Use `⟨(u : Fˣ ⧸ NE τ), fun σ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hgo, Units.val_mul, map_mul, hux]`. Conclude with `mul_pos (hxpos σ) (pos_of_hs (hCM σ) ((map_ne_zero σ).mpr n.ne_zero) (hs_map σ hnF))`.

Use extensionality with `v`. Rewrite using `[hS, hgo, hmulF, hs_map (cv v) hnF, mul_one, hux, hxloc v, hy]`. Distinguish the cases in `hv : v ∈ s`. Rewrite using `[if_pos hv]`. Conclude with `⟨fun _ => hv, fun _ => by norm_num⟩`.

Rewrite using `[if_neg hv]`. Conclude with `⟨fun h => absurd rfl h, fun h => absurd h hv⟩`. Establish `hb0 : ∀ v, ¬ (∃ y : (Kv v)ˣ, hs (cv v τ ^ 2 - 4) (y : Kv v) ≠ 1) → b v = 0` using `fun v h => by rw [hbdef, dif_neg h]`. Establish `hSg : ∀ g, ∀ v ∈ S g, v ∉ D.Sg` using `fun g v hv hvs => (hS g v).mp hv (hsplit v hvs _)`. Take `⟨A1, A2⟩` from `abs_sum D.Sg (fun g : Fˣ ⧸ NE τ => TPos ((g.out : Fˣ) : F)) S (fun v => ∃ y : (Kv v)ˣ, hs (cv v τ ^ 2 - 4) (y : Kv v) ≠ 1) (fun v => f v 1) b hab hb0 inj hSg ev surj`.

Establish `hterm : ∀ g : Fˣ ⧸ NE τ, D.nL c d (((g.out : Fˣ) : F) • m) = ∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), if v ∈ S g then b v else f v 1`. Introduce `g`. Unfold `Dat.nL`. Apply `finprod_congr` to reduce the goal to its premises. Introduce `v`.

Apply `finprod_congr` to reduce the goal to its premises. Introduce `hv`. Take `⟨p1, -, -⟩` from `loc v hv`. Establish `e` using `p1 (Units.map (cv v).toMonoidHom g.out)`. Rewrite `e` using `[hfdef v (Units.map (cv v).toMonoidHom g.out)]`.

Establish `hc : ((Units.map (cv v).toMonoidHom g.out : (Kv v)ˣ) : Kv v) = cv v ((g.out : Fˣ) : F)` using `rfl`. Rewrite `e` using `[hc]`. Rewrite using `[elmap_smul, e, ← hDv]`. Distinguish the cases in `h1 : hs (cv v (τ ^ 2 - 4)) (cv v ((g.out : Fˣ) : F)) = 1`. Rewrite using `[if_pos h1, if_neg (fun hm => (hS g v).mp hm h1)]`.

Rewrite using `[if_neg h1, if_pos ((hS g v).mpr h1)]`. Establish `R1 : (∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), stabSum (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m)) = ∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), (f v 1 + b v)` using `finprod_congr fun v => finprod_congr fun hv => (loc v hv).2.1`. Establish `R2 : (∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), kapSum (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m)) = ∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), (f v 1 - b v)` using `finprod_congr fun v => finprod_congr fun hv => (loc v hv).2.2`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Repeatedly rewrite using `[hterm]`.

Conclude with `A1`. Repeatedly rewrite using `[hterm]`. Rewrite using `[R1, R2]`. Conclude with `A2`.
-/
theorem sumT : SumT := by
  intro F _ _ Δ D hOk τ c d m hCM hSpl hDat
  have hD0 : τ ^ 2 - 4 ≠ 0 := hDat.reg
  have hDv : ∀ v : Pl F, cv v (τ ^ 2 - 4) = cv v τ ^ 2 - 4 := fun v => by
    rw [map_sub, map_pow, map_ofNat]
  have hCZ : ∀ v : Pl F, CharZero (Kv v) := fun v =>
    charZero_of_injective_algebraMap (algebraMap F (Kv v)).injective
  have hKne : ∀ v : Pl F, cv v (τ ^ 2 - 4) ≠ 0 := fun v => (map_ne_zero _).mpr hD0
  obtain ⟨f, hfdef⟩ : ∃ f : (v : Pl F) → (Kv v)ˣ → ℂ, ∀ v t, f v t =
      lcount (Ov v) (cv v c) (elmap (cv v) d) ((t : Kv v) • elmap (cv v) m) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : Pl F → ℂ, ∀ v, b v =
      if h : ∃ y : (Kv v)ˣ, hs (cv v τ ^ 2 - 4) (y : Kv v) ≠ 1 then f v h.choose else 0 :=
    ⟨_, fun _ => rfl⟩
  have hmulK : ∀ v : Pl F, ∀ x y : (Kv v)ˣ, hs (cv v τ ^ 2 - 4) ((x * y : (Kv v)ˣ) : Kv v) =
      hs (cv v τ ^ 2 - 4) (x : Kv v) * hs (cv v τ ^ 2 - 4) (y : Kv v) := by
    intro v x y
    rw [Units.val_mul]
    exact hsMul F v _ _ _ (by rw [← hDv]; exact hKne v) x.ne_zero y.ne_zero
  have loc : ∀ v, v ∉ D.Sg →
      (∀ t : (Kv v)ˣ, f v t = if hs (cv v τ ^ 2 - 4) (t : Kv v) = 1 then f v 1 else b v) ∧
      stabSum (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m) = f v 1 + b v ∧
      kapSum (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m) = f v 1 - b v := by
    intro v hv
    haveI := hCZ v
    have hDatv := (modelMap F (Kv v) (cv v) Δ τ c d m hDat).1
    have hinv : ∀ t ∈ NE (cv v τ), ∀ x : (Kv v)ˣ, f v (t * x) = f v x := by
      intro t ht x
      rw [hfdef, hfdef, Units.val_mul, mul_smul]
      exact lcountNorm (Ov v) (Kv v) _ _ (hOk.off v hv) _ _ _ (datSmul (Kv v) _ _ _ _ _ hDatv x) t ht
    obtain ⟨p1, p2, p3⟩ := loc_two (cv v τ) (hmulK v) (f v) hinv (b v) (hbdef v)
    refine ⟨p1, ?_, ?_⟩
    · unfold stabSum
      rw [← p2]
      exact finsum_congr fun q => (hfdef v _).symm
    · unfold kapSum
      rw [← p3]
      exact finsum_congr fun q => by rw [hfdef]
  have hab : ∀ᶠ v in Filter.cofinite, f v 1 = 1 ∧ b v = 0 := by
    filter_upwards [genPl F Δ D hOk τ c d m hDat] with v hv
    haveI := hCZ v
    refine ⟨?_, ?_⟩
    · rw [hfdef, hv 1]
      simp [one]
    · rw [hbdef]
      split_ifs with hex
      · rw [hfdef, hv, one, if_neg]
        rw [mem_NE]
        exact hex.choose_spec
      · rfl
  have hsplit : ∀ v ∈ D.Sg, ∀ z : Kv v, hs (cv v (τ ^ 2 - 4)) z = 1 := by
    intro v hv z
    haveI := hCZ v
    exact hs_sq (hKne v) (by rw [hDv]; exact hSpl v hv) z
  have hmulF : ∀ v (x y : Fˣ), hs (cv v (τ ^ 2 - 4)) (cv v ((x * y : Fˣ) : F)) =
      hs (cv v (τ ^ 2 - 4)) (cv v (x : F)) * hs (cv v (τ ^ 2 - 4)) (cv v (y : F)) := by
    intro v x y
    rw [Units.val_mul, map_mul]
    exact hsMul F v _ _ _ (hKne v) ((map_ne_zero _).mpr x.ne_zero) ((map_ne_zero _).mpr y.ne_zero)
  have hone : ∀ v, hs (cv v (τ ^ 2 - 4)) (cv v ((1 : Fˣ) : F)) = 1 := fun v => by
    rw [Units.val_one, map_one, hs_iff]
    exact ⟨1, 0, by ring⟩
  have hinvF : ∀ v (x : Fˣ), hs (cv v (τ ^ 2 - 4)) (cv v ((x⁻¹ : Fˣ) : F)) =
      hs (cv v (τ ^ 2 - 4)) (cv v (x : F)) := by
    intro v x
    have e := hmulF v x x⁻¹
    rw [mul_inv_cancel, hone] at e
    rcases hs_cases (cv v (τ ^ 2 - 4)) (cv v (x : F)) with h | h
    · rw [h] at e ⊢
      linear_combination -e
    · rw [h] at e ⊢
      linear_combination e
  have hrec := fun (x : Fˣ) => recip F (τ ^ 2 - 4) (x : F) hD0 x.ne_zero
  obtain ⟨S, hS⟩ : ∃ S : Fˣ ⧸ NE τ → Finset (Pl F), ∀ g v,
      v ∈ S g ↔ hs (cv v (τ ^ 2 - 4)) (cv v ((g.out : Fˣ) : F)) ≠ 1 :=
    ⟨fun g => (hrec g.out).1.toFinset, fun g v => Set.Finite.mem_toFinset _⟩
  have inj : ∀ g g' : Fˣ ⧸ NE τ, TPos ((g.out : Fˣ) : F) → TPos ((g'.out : Fˣ) : F) → S g = S g' → g = g' := by
    intro g g' hP hP' hSS
    rw [← QuotientGroup.out_eq' g, ← QuotientGroup.out_eq' g', QuotientGroup.eq, mem_NE]
    apply hsHasse F (τ ^ 2 - 4) _ hD0 (Units.ne_zero _)
    · intro σ
      apply hs_pos
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      exact mul_pos (inv_pos.mpr (hP σ)) (hP' σ)
    · intro v
      rw [hmulF, hinvF]
      by_cases hv : v ∈ D.Sg
      · simp only [hsplit v hv, mul_one]
      · have hiff : hs (cv v (τ ^ 2 - 4)) (cv v ((g.out : Fˣ) : F)) ≠ 1 ↔
            hs (cv v (τ ^ 2 - 4)) (cv v ((g'.out : Fˣ) : F)) ≠ 1 := (hS g v).symm.trans (hSS ▸ hS g' v)
        rcases hs_cases (cv v (τ ^ 2 - 4)) (cv v ((g.out : Fˣ) : F)) with h | h <;>
          rcases hs_cases (cv v (τ ^ 2 - 4)) (cv v ((g'.out : Fˣ) : F)) with h' | h'
        · rw [h, h']
          ring
        · exact absurd h (hiff.mpr (by rw [h']; norm_num))
        · exact absurd h' (hiff.mp (by rw [h]; norm_num))
        · rw [h, h']
          ring
  have ev : ∀ g : Fˣ ⧸ NE τ, TPos ((g.out : Fˣ) : F) → Even (S g).card := by
    intro g hP
    have hr := (hrec g.out).2
    have hreal : ∏ σ : F →+* ℝ, hs (σ (τ ^ 2 - 4)) (σ ((g.out : Fˣ) : F)) = 1 :=
      Finset.prod_eq_one fun σ _ => hs_pos _ (hP σ)
    have hsgn := finprod_sign (fun v => hs (cv v (τ ^ 2 - 4)) (cv v ((g.out : Fˣ) : F))) (S g) (by
      intro v
      by_cases hv : v ∈ S g
      · rw [if_pos hv]
        exact (hs_cases _ _).resolve_left ((hS g v).mp hv)
      · rw [if_neg hv]
        by_contra h
        exact hv ((hS g v).mpr h))
    rw [hsgn, hreal] at hr
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp hr
  have surj : ∀ s : Finset (Pl F), Even s.card →
      (∀ v ∈ s, ∃ y : (Kv v)ˣ, hs (cv v τ ^ 2 - 4) (y : Kv v) ≠ 1) →
      ∃ g : Fˣ ⧸ NE τ, TPos ((g.out : Fˣ) : F) ∧ S g = s := by
    intro s hs2 hE
    obtain ⟨y, hy⟩ : ∃ y : (v : Pl F) → (Kv v)ˣ, ∀ v,
        hs (cv v (τ ^ 2 - 4)) ((y v : (Kv v)ˣ) : Kv v) = if v ∈ s then -1 else 1 := by
      refine ⟨fun v => if h : v ∈ s then (hE v h).choose else 1, fun v => ?_⟩
      beta_reduce
      by_cases hv : v ∈ s
      · rw [if_pos hv, dif_pos hv]
        have hc := (hE v hv).choose_spec
        rw [hDv]
        exact (hs_cases _ _).resolve_left hc
      · rw [if_neg hv, dif_neg hv, Units.val_one, hs_iff]
        exact ⟨1, 0, by ring⟩
    have hfin : {v | hs (cv v (τ ^ 2 - 4)) ((y v : (Kv v)ˣ) : Kv v) ≠ 1}.Finite := by
      apply s.finite_toSet.subset
      intro v hv
      by_contra hvs
      apply hv
      rw [hy, if_neg (fun h => hvs (Finset.mem_coe.mpr h))]
    have hprod : ∏ᶠ v, hs (cv v (τ ^ 2 - 4)) ((y v : (Kv v)ˣ) : Kv v) = 1 := by
      rw [finprod_sign _ s hy]
      exact hs2.neg_one_pow
    obtain ⟨x, hx0, hxpos, hxloc⟩ := symbolEx F (τ ^ 2 - 4) hD0 y hfin hprod
    set u := Units.mk0 x hx0 with hu
    have hux : (u : F) = x := Units.val_mk0 _
    set n := u⁻¹ * (u : Fˣ ⧸ NE τ).out with hndef
    have hn : n ∈ NE τ := QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
    have hnF : hs (τ ^ 2 - 4) (n : F) = 1 := (mem_NE τ n).mp hn
    have hgo : ((u : Fˣ ⧸ NE τ).out : Fˣ) = u * n := (mul_inv_cancel_left u _).symm
    refine ⟨(u : Fˣ ⧸ NE τ), fun σ => ?_, ?_⟩
    · rw [hgo, Units.val_mul, map_mul, hux]
      exact mul_pos (hxpos σ) (pos_of_hs (hCM σ) ((map_ne_zero σ).mpr n.ne_zero) (hs_map σ hnF))
    · ext v
      rw [hS, hgo, hmulF, hs_map (cv v) hnF, mul_one, hux, hxloc v, hy]
      by_cases hv : v ∈ s
      · rw [if_pos hv]
        exact ⟨fun _ => hv, fun _ => by norm_num⟩
      · rw [if_neg hv]
        exact ⟨fun h => absurd rfl h, fun h => absurd h hv⟩
  have hb0 : ∀ v, ¬ (∃ y : (Kv v)ˣ, hs (cv v τ ^ 2 - 4) (y : Kv v) ≠ 1) → b v = 0 :=
    fun v h => by rw [hbdef, dif_neg h]
  have hSg : ∀ g, ∀ v ∈ S g, v ∉ D.Sg := fun g v hv hvs => (hS g v).mp hv (hsplit v hvs _)
  obtain ⟨A1, A2⟩ := abs_sum D.Sg (fun g : Fˣ ⧸ NE τ => TPos ((g.out : Fˣ) : F)) S
    (fun v => ∃ y : (Kv v)ˣ, hs (cv v τ ^ 2 - 4) (y : Kv v) ≠ 1) (fun v => f v 1) b hab hb0 inj hSg ev surj
  have hterm : ∀ g : Fˣ ⧸ NE τ, D.nL c d (((g.out : Fˣ) : F) • m) =
      ∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), if v ∈ S g then b v else f v 1 := by
    intro g
    unfold Dat.nL
    apply finprod_congr
    intro v
    apply finprod_congr
    intro hv
    obtain ⟨p1, -, -⟩ := loc v hv
    have e := p1 (Units.map (cv v).toMonoidHom g.out)
    rw [hfdef v (Units.map (cv v).toMonoidHom g.out)] at e
    have hc : ((Units.map (cv v).toMonoidHom g.out : (Kv v)ˣ) : Kv v) = cv v ((g.out : Fˣ) : F) := rfl
    rw [hc] at e
    rw [elmap_smul, e, ← hDv]
    by_cases h1 : hs (cv v (τ ^ 2 - 4)) (cv v ((g.out : Fˣ) : F)) = 1
    · rw [if_pos h1, if_neg (fun hm => (hS g v).mp hm h1)]
    · rw [if_neg h1, if_pos ((hS g v).mpr h1)]
  have R1 : (∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), stabSum (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m)) =
      ∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), (f v 1 + b v) :=
    finprod_congr fun v => finprod_congr fun hv => (loc v hv).2.1
  have R2 : (∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), kapSum (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m)) =
      ∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), (f v 1 - b v) :=
    finprod_congr fun v => finprod_congr fun hv => (loc v hv).2.2
  refine ⟨?_, ?_⟩
  · simp_rw [hterm]
    exact A1
  · simp_rw [hterm]
    rw [R1, R2]
    exact A2

end UpperTheory.V.Z.Sym.Glob
