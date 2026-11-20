import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckeCommRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.HeckeRestr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.HeckeModel
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLtOne
open IsLocalRing UpperTheory.V.Hi Matrix

namespace UpperTheory.V.Hi.Up

/- English proof (translation)
Use `haveI : Nontrivial A := φ.domain_nontrivial`. Set `κ` to `Module.Free.ChooseBasisIndex A Y`. Set `b : Module.Basis κ A Y` to `Module.Free.chooseBasis A Y`. Set `s : Y →ₛₗ[φ] E` to `{ toFun := fun y => sp y map_add' := fun y y' => hadd _ y.2 _ y'.2 map_smul' := fun c y => hsmul _ y.2 c }`. Set `L : (κ → K) →ₗ[K] E` to `Fintype.linearCombination K fun i => sp (b i)`.

Establish `hL : Function.Injective L` using `(hind κ b).fintypeLinearCombination_injective`. Establish `hs : ∀ y : Y, sp y = L fun i => φ (b.repr y i)`. Introduce `y`. Establish `: s y = s (∑ i, b.repr y i • b i)` using `by rw [b.sum_repr]`. Rewrite `this` using `[map_sum]`.

Simplify using `only [map_smulₛₗ] at this`. Conclude with `this`. Choose the witnesses or unpack the hypotheses as in `⟨w, rfl⟩ : F ∈ LinearMap.range L := by`. Use `(Submodule.span_le.2 ?_) hF` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `⟨_, (hs ⟨y, hy⟩).symm⟩`. Set `ρ : T →+* Matrix κ κ K` to `φ.mapMatrix.comp ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom.comp j.toRingHom)`. Establish `hρ : ∀ u i k, ρ u i k = φ (b.repr (j u (b k)) i)` using `fun u i k => congrArg φ (LinearMap.toMatrixAlgEquiv_apply b (j u) i k)`. Establish `hρt : ∀ i, ρ (t i) *ᵥ w = μ i • w`. Introduce `i`.

Use `hL ?_` and prove the remaining obligations. Rewrite using `[map_smul, ← hμ]`. Establish `: L ∘ₗ Matrix.toLin' (ρ (t i)) = opC i ∘ₗ L`. Use `LinearMap.pi_ext' fun k => LinearMap.ext_ring ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.single_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one]`.

Establish `h1 : L (Pi.single k 1) = sp (b k)` using `by simp [L]`. Rewrite using `[h1, ← hop i _ (b k).2, ← ht i, hs]`. Use `congr 1`. Use function extensionality and compare the values at `i'`. Conclude with `hρ _ _ _`.

Conclude with `LinearMap.congr_fun this w`. Establish `hρa : ∀ a, ρ (algebraMap A T a) *ᵥ w = φ a • w`. Introduce `a`. Establish `: ρ (algebraMap A T a) = φ a • (1 : Matrix κ κ K)`. Use extensionality with `i k`.

Rewrite using `[hρ, AlgHom.commutes, Module.algebraMap_end_apply, map_smul, b.repr_self]`. Distinguish the cases in `h : i = k`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Finsupp.single_apply, Ne.symm h]`.

Rewrite using `[this, smul_mulVec, one_mulVec]`. Establish `hall : ∀ u : T, ∃ c : K, ρ u *ᵥ w = c • w`. Introduce `u`. Establish `hu : u ∈ Algebra.adjoin A (Set.range t)` using `hgen ▸ Algebra.mem_top`. Proceed by induction on `hu using Algebra.adjoin_induction with`.

Consider the case `mem x hx => obtain ⟨i, rfl⟩ := hx`. Conclude with `⟨_, hρt i⟩`. Consider the case `algebraMap r => exact ⟨_, hρa r⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨c, hc⟩` from `hx`.

Take `⟨d, hd⟩` from `hy`. Conclude with `⟨c + d, by rw [map_add, add_mulVec, hc, hd, add_smul]⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨c, hc⟩` from `hx`. Take `⟨d, hd⟩` from `hy`.

Conclude with `⟨c * d, by rw [map_mul, ← mulVec_mulVec, hd, mulVec_smul, hc, smul_smul, mul_comm]⟩`. Use `choose χ hχ using hall`. Establish `hw : w ≠ 0` using `fun h => h0 (by rw [h, map_zero])`. Establish `hu : ∀ u c, ρ u *ᵥ w = c • w → χ u = c` using `fun u c h => smul_left_injective K hw ((hχ u).symm.trans h)`. Use `⟨{ toFun := χ map_one' := hu _ _ (by simp) map_mul' := fun x y => hu _ _ (by rw [map_mul, ← mulVec_mulVec, hχ, mulVec_smul, hχ, smul_smul, mul_comm]) map_zero' := hu _ _ (by simp) map_add' := fun x y => hu _ _ (by rw [map_add, add_mulVec, hχ, hχ, add_smul]) }, fun a => hu _ _ (hρ …` and prove the remaining obligations.
-/
theorem eigChar {A M ι K E T : Type} [CommRing A] [AddCommGroup M] [Module A M] [Field K] [AddCommGroup E] [Module K E]
    (Y : Submodule A M) [Module.Finite A Y] [Module.Free A Y] (op : ι → Module.End A M)
    [CommRing T] [Algebra A T] (j : T →ₐ[A] Module.End A Y) (t : ι → T) (ht : ∀ i, Restr (j (t i)) (op i))
    (hgen : Algebra.adjoin A (Set.range t) = ⊤)
    (φ : A →+* K) (sp : M → E) (hadd : ∀ f ∈ Y, ∀ f' ∈ Y, sp (f + f') = sp f + sp f')
    (hsmul : ∀ f ∈ Y, ∀ b : A, sp (b • f) = φ b • sp f)
    (hind : ∀ (κ : Type) (b : Module.Basis κ A Y), LinearIndependent K fun i => sp (b i))
    (opC : ι → Module.End K E) (hop : ∀ i, ∀ f ∈ Y, sp (op i f) = opC i (sp f))
    (F : E) (hF : F ∈ Submodule.span K (sp '' Y)) (h0 : F ≠ 0) (μ : ι → K) (hμ : ∀ i, opC i F = μ i • F) :
    ∃ χ : T →+* K, (∀ b, χ (algebraMap A T b) = φ b) ∧ ∀ i, χ (t i) = μ i := by
  classical
  haveI : Nontrivial A := φ.domain_nontrivial
  let κ := Module.Free.ChooseBasisIndex A Y
  let b : Module.Basis κ A Y := Module.Free.chooseBasis A Y
  let s : Y →ₛₗ[φ] E :=
    { toFun := fun y => sp y
      map_add' := fun y y' => hadd _ y.2 _ y'.2
      map_smul' := fun c y => hsmul _ y.2 c }
  let L : (κ → K) →ₗ[K] E := Fintype.linearCombination K fun i => sp (b i)
  have hL : Function.Injective L := (hind κ b).fintypeLinearCombination_injective
  have hs : ∀ y : Y, sp y = L fun i => φ (b.repr y i) := by
    intro y
    have : s y = s (∑ i, b.repr y i • b i) := by rw [b.sum_repr]
    rw [map_sum] at this
    simp only [map_smulₛₗ] at this
    exact this
  obtain ⟨w, rfl⟩ : F ∈ LinearMap.range L := by
    refine (Submodule.span_le.2 ?_) hF
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨_, (hs ⟨y, hy⟩).symm⟩
  let ρ : T →+* Matrix κ κ K :=
    φ.mapMatrix.comp ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom.comp j.toRingHom)
  have hρ : ∀ u i k, ρ u i k = φ (b.repr (j u (b k)) i) := fun u i k =>
    congrArg φ (LinearMap.toMatrixAlgEquiv_apply b (j u) i k)
  have hρt : ∀ i, ρ (t i) *ᵥ w = μ i • w := by
    intro i
    refine hL ?_
    rw [map_smul, ← hμ]
    have : L ∘ₗ Matrix.toLin' (ρ (t i)) = opC i ∘ₗ L := by
      refine LinearMap.pi_ext' fun k => LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, LinearMap.single_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one]
      have h1 : L (Pi.single k 1) = sp (b k) := by simp [L]
      rw [h1, ← hop i _ (b k).2, ← ht i, hs]
      congr 1
      funext i'
      exact hρ _ _ _
    exact LinearMap.congr_fun this w
  have hρa : ∀ a, ρ (algebraMap A T a) *ᵥ w = φ a • w := by
    intro a
    have : ρ (algebraMap A T a) = φ a • (1 : Matrix κ κ K) := by
      ext i k
      rw [hρ, AlgHom.commutes, Module.algebraMap_end_apply, map_smul, b.repr_self]
      by_cases h : i = k
      · subst h; simp
      · simp [h, Finsupp.single_apply, Ne.symm h]
    rw [this, smul_mulVec, one_mulVec]
  have hall : ∀ u : T, ∃ c : K, ρ u *ᵥ w = c • w := by
    intro u
    have hu : u ∈ Algebra.adjoin A (Set.range t) := hgen ▸ Algebra.mem_top
    induction hu using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact ⟨_, hρt i⟩
    | algebraMap r => exact ⟨_, hρa r⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨c + d, by rw [map_add, add_mulVec, hc, hd, add_smul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨c * d, by rw [map_mul, ← mulVec_mulVec, hd, mulVec_smul, hc, smul_smul, mul_comm]⟩
  choose χ hχ using hall
  have hw : w ≠ 0 := fun h => h0 (by rw [h, map_zero])
  have hu : ∀ u c, ρ u *ᵥ w = c • w → χ u = c := fun u c h => smul_left_injective K hw ((hχ u).symm.trans h)
  refine ⟨{ toFun := χ
            map_one' := hu _ _ (by simp)
            map_mul' := fun x y => hu _ _ (by rw [map_mul, ← mulVec_mulVec, hχ, mulVec_smul, hχ, smul_smul, mul_comm])
            map_zero' := hu _ _ (by simp)
            map_add' := fun x y => hu _ _ (by rw [map_add, add_mulVec, hχ, hχ, add_smul]) },
    fun a => hu _ _ (hρa a), fun i => hu _ _ (hρt i)⟩

/- English proof (translation)
Establish `hi : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Establish `h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x)` using `rfl`. Rewrite using `[h0, spectralValue_le_one_iff (minpoly.monic hi)]`. Prove the components needed by the constructor for the conclusion. Introduce `h n`.

Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]`. Conclude with `PadicInt.norm_le_one _`. Introduce `h`. Establish `hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l])` using `(Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)`.

Conclude with `⟨q, hqm, by rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩`.
-/
theorem intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

open Polynomial in
/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.NormLtOne.norm_lt_one y a ha`.
-/
theorem normLt {l : ℕ} [Fact l.Prime] {O R : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [CommRing R] [IsLocalRing R] [Algebra O R]
    (y : R →ₐ[O] PadicAlgCl l) (a : R) (ha : a ∈ maximalIdeal R) : ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.NormLtOne.norm_lt_one y a ha

/- English proof (translation)
Take `⟨T, _, _, j, t, hj, hr, ht, hgen, -⟩` from `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeModel A M ι Y op hC`. Take `⟨χ, h1, h2⟩` from `eigChar Y op j t ht hgen (e.toRingHom.comp x) sp hadd hsmul hind opC hop F hF h0 μ hμ`. Set `χ' : T →+* PadicAlgCl l` to `e.symm.toRingHom.comp χ`. Establish `h1' : ∀ b, χ' (algebraMap A T b) = x b` using `fun b => by`. Express the relevant statement in the definitionally equal form `e.symm (χ _) = _`.

Rewrite using `[h1]`. Conclude with `e.symm_apply_apply _`. Establish `h2' : ∀ i, χ' (t i) = e.symm (μ i)` using `fun i => congrArg e.symm (h2 i)`. Establish `hmem : ∀ u, χ' u ∈ Valued.integer (PadicAlgCl l)`. Introduce `u`.

Establish `hu : u ∈ Algebra.adjoin A (Set.range t)` using `hgen ▸ Algebra.mem_top`. Proceed by induction on `hu using Algebra.adjoin_induction with`. Consider the case `mem x' hx`. Take `⟨i, rfl⟩` from `hx`. Establish `: χ' (t i) = (e.symm (μ i) - x (a i)) + x (a i)` using `by rw [h2']; ring`.

Rewrite using `[this]`. Conclude with `add_mem (Valued.integer.mem_iff.2 (ha i).le) (Valued.integer.mem_iff.2 (hx1 _))`. Consider the case `algebraMap r => rw [h1']`. Conclude with `Valued.integer.mem_iff.2 (hx1 _)`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `mul_mem hx hy`. Use `haveI : IsLocalRing (Valued.integer (PadicAlgCl l)) := inferInstanceAs (IsLocalRing (Valued.v (R := PadicAlgCl l)).valuationSubring)`. Establish `hm : ∀ z : Valued.integer (PadicAlgCl l), ‖(z : PadicAlgCl l)‖ < 1 → z ∈ maximalIdeal _` using `fun z hz hu => hz.ne (Valued.integer.isUnit_iff_norm_eq_one.1 hu)`.

Take `⟨r, -, hr2, hr3⟩` from `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeRestr A M ι Y op a hC T (heckeAlg (locPart Y op a) op) j (Subalgebra.val _) hj hr Subtype.val_injective (Subalgebra.range_val _)`. Take `⟨hne, x', hx'⟩` from `hr3 (Valued.integer (PadicAlgCl l)) (χ'.codRestrict _ hmem) (fun c hc => hm _ (by`. Express the relevant statement in the definitionally equal form `‖χ' _‖ < 1`. Rewrite using `[h1']`. Conclude with `hx2 c hc))`.

Use the proof step `(fun i s hs => hm _ (by`. Establish `: s = t i` using `hj (LinearMap.ext fun y => Subtype.ext ((hs y).trans (ht i y).symm))`. Express the relevant statement in the definitionally equal form `‖χ' _ - χ' _‖ < 1`. Rewrite using `[this, h1', h2']`. Conclude with `ha i))`.

Establish `hx'' : ∀ u, (x' (r u) : PadicAlgCl l) = χ' u` using `fun u => congrArg Subtype.val (RingHom.congr_fun hx' u)`. Use `⟨hne, (Subring.subtype _).comp x', fun b => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← r.commutes, ← h1']`. Conclude with `hx'' _`. Establish `: r (t i) = heckeGen _ op i` using `Subtype.ext (LinearMap.ext fun y => Subtype.ext ((hr2 (t i) y).trans (ht i _)))`.

Rewrite using `[← this]`. Express the relevant statement in the definitionally equal form `e (x' (r (t i)) : PadicAlgCl l) = _`. Rewrite using `[hx'', h2']`. Conclude with `e.apply_symm_apply _`.
-/
theorem eigPt {l : ℕ} [Fact l.Prime] {A M ι E : Type} [CommRing A] [IsCNL A] [AddCommGroup M] [Module A M]
    [AddCommGroup E] [Module ℂ E]
    (Y : Submodule A M) [Module.Finite A Y] [Module.Free A Y] (op : ι → Module.End A M) (hC : CommOn Y op)
    (e : PadicAlgCl l ≃+* ℂ) (x : A →+* PadicAlgCl l) (hx1 : ∀ b, ‖x b‖ ≤ 1) (hx2 : ∀ b ∈ maximalIdeal A, ‖x b‖ < 1)
    (sp : M → E) (hadd : ∀ f ∈ Y, ∀ f' ∈ Y, sp (f + f') = sp f + sp f')
    (hsmul : ∀ f ∈ Y, ∀ b : A, sp (b • f) = e (x b) • sp f)
    (hind : ∀ (κ : Type) (b : Module.Basis κ A Y), LinearIndependent ℂ fun i => sp (b i))
    (opC : ι → Module.End ℂ E) (hop : ∀ i, ∀ f ∈ Y, sp (op i f) = opC i (sp f))
    (F : E) (hF : F ∈ Submodule.span ℂ (sp '' Y)) (h0 : F ≠ 0) (μ : ι → ℂ) (hμ : ∀ i, opC i F = μ i • F)
    (a : ι → A) (ha : ∀ i, ‖e.symm (μ i) - x (a i)‖ < 1) [Fact (CommOn (locPart Y op a) op)] :
    locPart Y op a ≠ ⊥ ∧ ∃ y : heckeAlg (locPart Y op a) op →+* PadicAlgCl l,
      (∀ b, y (algebraMap A _ b) = x b) ∧ ∀ i, e (y (heckeGen _ op i)) = μ i := by
  obtain ⟨T, _, _, j, t, hj, hr, ht, hgen, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeModel A M ι Y op hC
  obtain ⟨χ, h1, h2⟩ := eigChar Y op j t ht hgen (e.toRingHom.comp x) sp hadd hsmul hind opC hop F hF h0 μ hμ
  let χ' : T →+* PadicAlgCl l := e.symm.toRingHom.comp χ
  have h1' : ∀ b, χ' (algebraMap A T b) = x b := fun b => by
    change e.symm (χ _) = _
    rw [h1]; exact e.symm_apply_apply _
  have h2' : ∀ i, χ' (t i) = e.symm (μ i) := fun i => congrArg e.symm (h2 i)
  have hmem : ∀ u, χ' u ∈ Valued.integer (PadicAlgCl l) := by
    intro u
    have hu : u ∈ Algebra.adjoin A (Set.range t) := hgen ▸ Algebra.mem_top
    induction hu using Algebra.adjoin_induction with
    | mem x' hx =>
      obtain ⟨i, rfl⟩ := hx
      have : χ' (t i) = (e.symm (μ i) - x (a i)) + x (a i) := by rw [h2']; ring
      rw [this]
      exact add_mem (Valued.integer.mem_iff.2 (ha i).le) (Valued.integer.mem_iff.2 (hx1 _))
    | algebraMap r => rw [h1']; exact Valued.integer.mem_iff.2 (hx1 _)
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  haveI : IsLocalRing (Valued.integer (PadicAlgCl l)) :=
    inferInstanceAs (IsLocalRing (Valued.v (R := PadicAlgCl l)).valuationSubring)
  have hm : ∀ z : Valued.integer (PadicAlgCl l), ‖(z : PadicAlgCl l)‖ < 1 → z ∈ maximalIdeal _ := fun z hz hu =>
    hz.ne (Valued.integer.isUnit_iff_norm_eq_one.1 hu)
  obtain ⟨r, -, hr2, hr3⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeRestr A M ι Y op a hC T (heckeAlg (locPart Y op a) op) j
    (Subalgebra.val _) hj hr Subtype.val_injective (Subalgebra.range_val _)
  obtain ⟨hne, x', hx'⟩ := hr3 (Valued.integer (PadicAlgCl l)) (χ'.codRestrict _ hmem)
    (fun c hc => hm _ (by
      change ‖χ' _‖ < 1
      rw [h1']; exact hx2 c hc))
    (fun i s hs => hm _ (by
      have : s = t i := hj (LinearMap.ext fun y => Subtype.ext ((hs y).trans (ht i y).symm))
      change ‖χ' _ - χ' _‖ < 1
      rw [this, h1', h2']; exact ha i))
  have hx'' : ∀ u, (x' (r u) : PadicAlgCl l) = χ' u := fun u => congrArg Subtype.val (RingHom.congr_fun hx' u)
  refine ⟨hne, (Subring.subtype _).comp x', fun b => ?_, fun i => ?_⟩
  · rw [← r.commutes, ← h1']; exact hx'' _
  · have : r (t i) = heckeGen _ op i :=
      Subtype.ext (LinearMap.ext fun y => Subtype.ext ((hr2 (t i) y).trans (ht i _)))
    rw [← this]
    change e (x' (r (t i)) : PadicAlgCl l) = _
    rw [hx'', h2']; exact e.apply_symm_apply _

end UpperTheory.V.Hi.Up
