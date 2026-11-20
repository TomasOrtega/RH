import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.TopLeCopiesSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.RepAvg
open GlobalTheory.PRep Matrix UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
open scoped ComplexOrder

namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

section SlopeTestRemainingChoices

variable {k H V : Type} [Field k] [Group H] [AddCommGroup V] [Module k V]

private def ecStab (T : Representation k H V) (v : V) : Subgroup H where
  carrier := {g | T g v = v}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

/- English proof (translation)
Take `⟨s, hs⟩` from `QuotientGroup.mk_out_eq_mul S g`. Establish `h : T s v = v` using `hS s.2`. Rewrite using `[hs, map_mul, Module.End.mul_apply, h]`.
-/
private theorem ec_out (T : Representation k H V) (v : V) (S : Subgroup H) (hS : S ≤ ecStab T v) (g : H) :
    T ((g : H ⧸ S).out) v = T g v := by
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S g
  have h : T s v = v := hS s.2
  rw [hs, map_mul, Module.End.mul_apply, h]

/- English proof (translation)
Use `Fintype.sum_equiv (Equiv.mulRight (n : H ⧸ S)) _ _ fun q => ?_` and prove the remaining obligations. Establish `: Equiv.mulRight (n : H ⧸ S) q = ((q.out * n : H) : H ⧸ S)`. Simplify using the standard rewrite rules. Rewrite using `[this, ec_out T v S hS, map_mul, Module.End.mul_apply]`.
-/
private theorem ec_right (T : Representation k H V) (v : V) (S : Subgroup H) [S.Normal] [Fintype (H ⧸ S)]
    (hS : S ≤ ecStab T v) (n : H) :
    ∑ q : H ⧸ S, T q.out (T n v) = ∑ q : H ⧸ S, T q.out v := by
  refine Fintype.sum_equiv (Equiv.mulRight (n : H ⧸ S)) _ _ fun q => ?_
  have : Equiv.mulRight (n : H ⧸ S) q = ((q.out * n : H) : H ⧸ S) := by
    simp
  rw [this, ec_out T v S hS, map_mul, Module.End.mul_apply]

/- English proof (translation)
Rewrite using `[map_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft (n : H ⧸ S)) _ _ fun q => ?_` and prove the remaining obligations. Establish `: Equiv.mulLeft (n : H ⧸ S) q = ((n * q.out : H) : H ⧸ S)`. Simplify using the standard rewrite rules. Rewrite using `[this, ec_out T v S hS, map_mul, Module.End.mul_apply]`.
-/
private theorem ec_left (T : Representation k H V) (v : V) (S : Subgroup H) [S.Normal] [Fintype (H ⧸ S)]
    (hS : S ≤ ecStab T v) (n : H) :
    T n (∑ q : H ⧸ S, T q.out v) = ∑ q : H ⧸ S, T q.out v := by
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (n : H ⧸ S)) _ _ fun q => ?_
  have : Equiv.mulLeft (n : H ⧸ S) q = ((n * q.out : H) : H ⧸ S) := by
    simp
  rw [this, ec_out T v S hS, map_mul, Module.End.mul_apply]

variable {G : Type} [Group G]

private def ecTw (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ) : Representation k K V where
  toFun x := (((χ x)⁻¹ : kˣ) : k) • ρ x
  map_one' := by simp
  map_mul' a b := by
    ext v
    simp [smul_smul, mul_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem ecTw_apply (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ) (x : K) (v : V) :
    ecTw ρ K χ x v = (((χ x)⁻¹ : kˣ) : k) • ρ x v := rfl

/- English proof (translation)
Rewrite using `[ecTw_apply, smul_smul]`. Simplify using the standard rewrite rules.
-/
private theorem ecTw_smul (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ) (x : K) (v : V) :
    ρ x v = (χ x : k) • ecTw ρ K χ x v := by
  rw [ecTw_apply, smul_smul]
  simp

/- English proof (translation)
Use `forall_congr' fun x => ?_` and prove the remaining obligations. Rewrite using `[ecTw_smul ρ K χ]`. Conclude with `smul_right_inj (χ x).ne_zero`.
-/
private theorem ec_mem_eig (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ) (v : V) :
    v ∈ eig ρ K χ ↔ ∀ x, ecTw ρ K χ x v = v := by
  refine forall_congr' fun x => ?_
  rw [ecTw_smul ρ K χ]
  exact smul_right_inj (χ x).ne_zero

/- English proof (translation)
Establish `h : ρ x v - (χ x : k) • v ∈ twKer ρ K χ` using `Submodule.subset_span ⟨x, v, rfl⟩`. Establish `h2` using `(twKer ρ K χ).smul_mem (-(((χ x)⁻¹ : kˣ) : k)) h`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[ecTw_apply, smul_sub, smul_smul]`. Simplify using the standard rewrite rules.

Normalize the expressions using the abelian group laws.
-/
private theorem ec_mem_tw (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ) (x : K) (v : V) :
    v - ecTw ρ K χ x v ∈ twKer ρ K χ := by
  have h : ρ x v - (χ x : k) • v ∈ twKer ρ K χ := Submodule.subset_span ⟨x, v, rfl⟩
  have h2 := (twKer ρ K χ).smul_mem (-(((χ x)⁻¹ : kˣ) : k)) h
  convert h2 using 1
  rw [ecTw_apply, smul_sub, smul_smul]
  simp
  abel

/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Establish `ho : IsOpen (ecStab (ecTw ρ K χ) v : Set K)`. Establish `h1 : IsOpen ((fun x : K => (x : G)) ⁻¹' {g : G | ρ g v = v})` using `(hρ v).preimage continuous_subtype_val`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((h1.inter hχ).mem_nhds (by simp)) ?_)` and prove the remaining obligations. Introduce and unpack `x ⟨hx1, hx2⟩`.

Establish `a : ρ x v = v` using `hx1`. Establish `b : χ x = 1` using `hx2`. Use `show ecTw ρ K χ x v = v`. Rewrite using `[ecTw_apply, a, b]`. Simplify using the standard rewrite rules.

Use `haveI := Subgroup.quotient_finite_of_isOpen _ ho`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`.
-/
private theorem ec_fin [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation k G V) (K : Subgroup G)
    (χ : K →* kˣ) (hρ : IsSmooth ρ) (hK : IsCompact (K : Set G)) (hχ : IsOpen {x : K | χ x = 1}) (v : V) :
    (ecStab (ecTw ρ K χ) v).FiniteIndex := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen (ecStab (ecTw ρ K χ) v : Set K) := by
    have h1 : IsOpen ((fun x : K => (x : G)) ⁻¹' {g : G | ρ g v = v}) := (hρ v).preimage continuous_subtype_val
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset ((h1.inter hχ).mem_nhds (by simp)) ?_)
    rintro x ⟨hx1, hx2⟩
    have a : ρ x v = v := hx1
    have b : χ x = 1 := hx2
    show ecTw ρ K χ x v = v
    rw [ecTw_apply, a, b]
    simp
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.finiteIndex_of_finite_quotient

end SlopeTestRemainingChoices

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

/- English proof (translation)
Introduce `k G V _ _ _ _ _ _ _ ρ K χ hρ hK hχ`. Establish `hfin` using `ec_fin ρ K χ hρ hK hχ`. Establish `part2 : ∀ W : Submodule k V, (∀ x ∈ K, ∀ v ∈ W, ρ x v ∈ W) → ∀ v ∈ W, ∃ w ∈ W, w ∈ eig ρ K χ ∧ v - w ∈ twKer ρ K χ`. Introduce `W hW v hv`. Use `haveI := hfin v`.

Use `set S := (ecStab (ecTw ρ K χ) v).normalCore with hSdef`. Establish `hS : S ≤ ecStab (ecTw ρ K χ) v` using `Subgroup.normalCore_le _`. Use `letI : Fintype (K ⧸ S) := Fintype.ofFinite _`. Establish `hc : (Fintype.card (K ⧸ S) : k) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Use `⟨(Fintype.card (K ⧸ S) : k)⁻¹ • ∑ q : K ⧸ S, ecTw ρ K χ q.out v, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `W.smul_mem _ (W.sum_mem fun q _ => W.smul_mem _ (hW _ q.out.2 v hv))`. Conclude with `Submodule.smul_mem _ _ ((ec_mem_eig ρ K χ _).2 fun x => ec_left _ v S hS x)`. Establish `: v - (Fintype.card (K ⧸ S) : k)⁻¹ • ∑ q : K ⧸ S, ecTw ρ K χ q.out v = (Fintype.card (K ⧸ S) : k)⁻¹ • ∑ q : K ⧸ S, (v - ecTw ρ K χ q.out v)`. Rewrite using `[Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, inv_smul_smul₀ hc]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ec_mem_tw ρ K χ _ v)`. Establish `key : ∀ w ∈ twKer ρ K χ, ∃ S₀ : Subgroup K, S₀.FiniteIndex ∧ ∀ (S : Subgroup K) [S.Normal] [Fintype (K ⧸ S)], S ≤ S₀ → ∑ q : K ⧸ S, ecTw ρ K χ q.out w = 0`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`.

Take `⟨n, u, rfl⟩` from `hw`. Use `⟨_, hfin u, fun S _ _ hS => ?_⟩` and prove the remaining obligations. Rewrite using `[ecTw_smul ρ K χ]`. Simplify using `only [map_sub, map_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]`. Rewrite using `[ec_right _ u S hS, sub_self]`.

Consider the case `zero => exact ⟨⊤, inferInstance, fun S _ _ _ => by simp⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨A, hA, ha⟩` from `ha`. Take `⟨B, hB, hb⟩` from `hb`. Use `⟨A ⊓ B, inferInstance, fun S _ _ hS => ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, Finset.sum_add_distrib]`. Rewrite using `[ha S (hS.trans inf_le_left), hb S (hS.trans inf_le_right), add_zero]`. Consider the case `smul c a _ ha`. Take `⟨A, hA, ha⟩` from `ha`. Use `⟨A, hA, fun S _ _ hS => ?_⟩` and prove the remaining obligations.

Simplify using `only [map_smul, ← Finset.smul_sum]`. Rewrite using `[ha S hS, smul_zero]`. Use `⟨⟨?_, ?_⟩, part2⟩` and prove the remaining obligations. Rewrite using `[Submodule.disjoint_def]`. Introduce `w he hw`.

Take `⟨A, hA, h⟩` from `key w hw`. Use `letI : Fintype (K ⧸ A.normalCore) := Fintype.ofFinite _`. Establish `hc : (Fintype.card (K ⧸ A.normalCore) : k) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Establish `h2` using `h A.normalCore A.normalCore_le`. Simplify using `only [(ec_mem_eig ρ K χ w).1 he, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k] at h2`.

Conclude with `(smul_eq_zero.1 h2).resolve_left hc`. Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `v _`. Take `⟨w, -, h1, h2⟩` from `part2 ⊤ (fun _ _ _ _ => trivial) v trivial`. Use `Submodule.add_mem_sup h1 h2` as an intermediate fact.

Simplify using `using this`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.repEigCompl :
    ∀ {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [CharZero k] [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ), IsSmooth ρ → IsCompact (K : Set G) → IsOpen {x : K | χ x = 1} → IsCompl (eig ρ K χ) (twKer ρ K χ) ∧ ∀ W : Submodule k V, (∀ x ∈ K, ∀ v ∈ W, ρ x v ∈ W) → ∀ v ∈ W, ∃ w ∈ W, w ∈ eig ρ K χ ∧ v - w ∈ twKer ρ K χ := by
  intro k G V _ _ _ _ _ _ _ ρ K χ hρ hK hχ
  have hfin := ec_fin ρ K χ hρ hK hχ
  have part2 : ∀ W : Submodule k V, (∀ x ∈ K, ∀ v ∈ W, ρ x v ∈ W) → ∀ v ∈ W,
      ∃ w ∈ W, w ∈ eig ρ K χ ∧ v - w ∈ twKer ρ K χ := by
    intro W hW v hv
    haveI := hfin v
    set S := (ecStab (ecTw ρ K χ) v).normalCore with hSdef
    have hS : S ≤ ecStab (ecTw ρ K χ) v := Subgroup.normalCore_le _
    letI : Fintype (K ⧸ S) := Fintype.ofFinite _
    have hc : (Fintype.card (K ⧸ S) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    refine ⟨(Fintype.card (K ⧸ S) : k)⁻¹ • ∑ q : K ⧸ S, ecTw ρ K χ q.out v, ?_, ?_, ?_⟩
    · exact W.smul_mem _ (W.sum_mem fun q _ => W.smul_mem _ (hW _ q.out.2 v hv))
    · exact Submodule.smul_mem _ _ ((ec_mem_eig ρ K χ _).2 fun x => ec_left _ v S hS x)
    · have : v - (Fintype.card (K ⧸ S) : k)⁻¹ • ∑ q : K ⧸ S, ecTw ρ K χ q.out v =
          (Fintype.card (K ⧸ S) : k)⁻¹ • ∑ q : K ⧸ S, (v - ecTw ρ K χ q.out v) := by
        rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k,
          inv_smul_smul₀ hc]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ec_mem_tw ρ K χ _ v)
  have key : ∀ w ∈ twKer ρ K χ, ∃ S₀ : Subgroup K, S₀.FiniteIndex ∧
      ∀ (S : Subgroup K) [S.Normal] [Fintype (K ⧸ S)], S ≤ S₀ → ∑ q : K ⧸ S, ecTw ρ K χ q.out w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨n, u, rfl⟩ := hw
      refine ⟨_, hfin u, fun S _ _ hS => ?_⟩
      rw [ecTw_smul ρ K χ]
      simp only [map_sub, map_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
      rw [ec_right _ u S hS, sub_self]
    | zero => exact ⟨⊤, inferInstance, fun S _ _ _ => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨A, hA, ha⟩ := ha
      obtain ⟨B, hB, hb⟩ := hb
      refine ⟨A ⊓ B, inferInstance, fun S _ _ hS => ?_⟩
      simp only [map_add, Finset.sum_add_distrib]
      rw [ha S (hS.trans inf_le_left), hb S (hS.trans inf_le_right), add_zero]
    | smul c a _ ha =>
      obtain ⟨A, hA, ha⟩ := ha
      refine ⟨A, hA, fun S _ _ hS => ?_⟩
      simp only [map_smul, ← Finset.smul_sum]
      rw [ha S hS, smul_zero]
  refine ⟨⟨?_, ?_⟩, part2⟩
  · rw [Submodule.disjoint_def]
    intro w he hw
    obtain ⟨A, hA, h⟩ := key w hw
    letI : Fintype (K ⧸ A.normalCore) := Fintype.ofFinite _
    have hc : (Fintype.card (K ⧸ A.normalCore) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have h2 := h A.normalCore A.normalCore_le
    simp only [(ec_mem_eig ρ K χ w).1 he, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k] at h2
    exact (smul_eq_zero.1 h2).resolve_left hc
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    obtain ⟨w, -, h1, h2⟩ := part2 ⊤ (fun _ _ _ _ => trivial) v trivial
    have := Submodule.add_mem_sup h1 h2
    simpa using this
