import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsLeastOfDiscrete
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRepresentativesModNsmul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfEq
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FamEqOnClassOfEq

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitBallFree

/- English proof (translation)
Use `choose t ht0 htq htd using ht`. Establish `key : ∀ (c : Fin n → F) (p : J), φ (∑ i, c i • (t (e i) • B (e i))) p = c (e.symm p) * t p`. Introduce `c p`. Simplify using `only [map_sum, map_smul, hB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]`. Rewrite using `[Finset.sum_eq_single (e.symm p)]`.

Simplify using the standard rewrite rules. Introduce `i _ hi`. Establish `hne : p ≠ e i` using `fun h => hi (by rw [h, Equiv.symm_apply_apply])`. Simplify using `[hne]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Use `⟨fun i => t (e i) • B (e i), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Establish `h1` using `congrFun (congrArg φ hg) (e i)`.

Rewrite `h1` using `[key g (e i), map_zero, Equiv.symm_apply_apply]`. Conclude with `(mul_eq_zero.1 h1).resolve_right (ht0 _)`. Introduce `i`. Rewrite using `[hP]`. Introduce `p`.

Rewrite using `[map_smul, hB]`. Distinguish the cases in `h : p = e i`. Substitute `h` using the available equality. Simplify using `using htq (e i)`. Simplify using `[h]`.

Introduce `s`. Prove the components needed by the constructor for the conclusion. Introduce `hs`. Rewrite `hs` using `[hP]`. Use `choose c hc0 hce using fun p => htd p _ (hs p)`.

Use `⟨fun i => c (e i), fun i => hc0 _, hφ ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Rewrite using `[key, Equiv.apply_symm_apply, hce p]`. Introduce and unpack `⟨c, hc, rfl⟩`. Rewrite using `[hP]`.

Introduce `p`. Rewrite using `[key, AddValuation.map_mul]`. Simplify using `using add_le_add (hc (e.symm p)) (htq p)`.
-/
theorem exists_basis_of_coord {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {M : Type*} [AddCommGroup M]
    [Module F M] {J : Type} [Fintype J] [DecidableEq J] (φ : M →ₗ[F] (J → F)) (hφ : Function.Injective φ)
    (B : J → M) (hB : ∀ p, φ (B p) = Pi.single p 1) (q : J → ℚ)
    (ht : ∀ p, ∃ t : F, t ≠ 0 ∧ ((q p : ℚ) : WithTop ℚ) ≤ v t ∧
      ∀ a : F, ((q p : ℚ) : WithTop ℚ) ≤ v a → ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧ a = c * t)
    (P : M → Prop) (hP : ∀ s, P s ↔ ∀ p, ((q p : ℚ) : WithTop ℚ) ≤ v (φ s p)) {n : ℕ} (e : Fin n ≃ J) :
    ∃ b : Fin n → M, LinearIndependent F b ∧ (∀ i, P (b i)) ∧
      ∀ s : M, P s ↔ ∃ c : Fin n → F, (∀ i, (0 : WithTop ℚ) ≤ v (c i)) ∧ s = ∑ i, c i • b i := by
  choose t ht0 htq htd using ht

  have key : ∀ (c : Fin n → F) (p : J), φ (∑ i, c i • (t (e i) • B (e i))) p = c (e.symm p) * t p := by
    intro c p
    simp only [map_sum, map_smul, hB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [Finset.sum_eq_single (e.symm p)]
    · simp
    · intro i _ hi
      have hne : p ≠ e i := fun h => hi (by rw [h, Equiv.symm_apply_apply])
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine ⟨fun i => t (e i) • B (e i), ?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := congrFun (congrArg φ hg) (e i)
    rw [key g (e i), map_zero, Equiv.symm_apply_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_right (ht0 _)
  · intro i
    rw [hP]
    intro p
    rw [map_smul, hB]
    by_cases h : p = e i
    · subst h
      simpa using htq (e i)
    · simp [h]
  · intro s
    constructor
    · intro hs
      rw [hP] at hs
      choose c hc0 hce using fun p => htd p _ (hs p)
      refine ⟨fun i => c (e i), fun i => hc0 _, hφ ?_⟩
      funext p
      rw [key, Equiv.apply_symm_apply, hce p]
    · rintro ⟨c, hc, rfl⟩
      rw [hP]
      intro p
      rw [key, AddValuation.map_mul]
      simpa using add_le_add (hc (e.symm p)) (htq p)

/- English proof (translation)
Introduce `hG hTw V _ _ _ ϖ hϖ D Q hQ F _ _ v hv hF k hk`. Take `⟨hinj, e0, he0⟩` from `GlobalTheory.exists_representatives_mod_nsmul D.toPre.X k hk`. Use `choose bb hbb using fun i => GlobalTheory.IntegralCoord.main hTw V ϖ hϖ D F v hv k hk (e0 i)`. Use `choose crd crd_spec using fun (s : Fam D.toPre F k) i => ((hbb i).1 (s.s (e0 i))).exists`. Establish `hadd : ∀ (s t : Fam D.toPre F k) i, crd (s + t) i = fun c => crd s i c + crd t i c`.

Introduce `s t i`. Use `((hbb i).1 _).unique (crd_spec _ i) ?_` and prove the remaining obligations. Introduce `j`. Rewrite using `[add_f, crd_spec s i j, crd_spec t i j, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[constBF_eq, constBF_eq, constBF_eq]`. Simplify using `only [map_add, resTop, add_mul]`. Establish `hsmul : ∀ (ζ : F) (s : Fam D.toPre F k) i, crd (ζ • s) i = fun c => ζ * crd s i c`. Introduce `ζ s i`. Use `((hbb i).1 _).unique (crd_spec _ i) ?_` and prove the remaining obligations.

Introduce `j`. Rewrite using `[smul_f, crd_spec s i j, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[constBF_eq, constBF_eq]`. Simplify using `only [map_mul, resTop, _root_.mul_assoc]`.

Set `φ : Fam D.toPre F k →ₗ[F] (Fin (k ^ Module.finrank ℤ D.toPre.X) × Fin (k ^ D.toPre.P.g) → F)` to `{ toFun := fun s p => crd s p.1 p.2 map_add' := fun s t => by`. Use function extensionality and compare the values at `p`. Simplify using `only [hadd, Pi.add_apply]`. Use the proof step `map_smul' := fun ζ s => by`. Use function extensionality and compare the values at `p`.

Simplify using `only [hsmul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul] }`. Establish `hφ : Function.Injective φ`. Introduce `s t h`. Apply `fam_ext` to reduce the goal to its premises. Introduce `χ j`.

Take `⟨i, ⟨m, rfl⟩, -⟩` from `he0 χ`. Establish `hag : ∀ j, (s.s (e0 i)).f j = (t.s (e0 i)).f j`. Introduce `j`. Rewrite using `[crd_spec s i j, crd_spec t i j]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[show crd s i c = crd t i c from congrFun h (i, c)]`. Conclude with `GlobalTheory.fam_eq_on_class_of_eq hG V D.toPre F k s t (e0 i) hag m j`. Establish `hcls : ∀ i (a b : D.toPre.X), e0 i + k • a = e0 i + k • b → a = b` using `fun i a b h => hinj a b (add_left_cancel h)`. Use `choose B hB1 hB2 using fun p : Fin (k ^ Module.finrank ℤ D.toPre.X) × Fin (k ^ D.toPre.P.g) => ReciprocityTheory.ChartRestriction.G.DVR.UUA.exists_fam_rep hG D.tau_bimult k (e0 p.1) (hcls p.1) (bb p.1 p.2)`. Establish `hB : ∀ p, φ (B p) = Pi.single p 1`.

Introduce and unpack `⟨i, c⟩`. Use function extensionality and compare the values at `⟨i', c'⟩`. Use `show crd (B (i, c)) i' c' = _`. Distinguish the cases in `hi : i' = i`. Substitute `hi` using the available equality.

Establish `h1 : crd (B (i', c)) i' = Pi.single c 1`. Use `((hbb i').1 _).unique (crd_spec _ i') ?_` and prove the remaining obligations. Introduce `j`. Rewrite using `[hB1, Finset.sum_eq_single c]`. Rewrite using `[constBF_eq]`.

Simplify using `[resTop]`. Introduce `b _ hb`. Rewrite using `[constBF_eq]`. Simplify using `[resTop, hb]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[h1]`. Distinguish the cases in `hc : c' = c`. Substitute `hc` using the available equality. Simplify using the standard rewrite rules.

Establish `hne : (i', c') ≠ (i', c)` using `fun h => hc (Prod.ext_iff.1 h).2`. Simplify using `[hc, hne]`. Establish `hz : ∀ j, ((B (i, c)).s (e0 i')).f j = 0`. Use `hB2 (i, c) (e0 i') fun mu h => hi ?_` and prove the remaining obligations. Conclude with `((he0 (e0 i')).unique ⟨0, by simp⟩ ⟨mu, h.symm⟩)`.

Establish `h1 : crd (B (i, c)) i' = 0`. Use `((hbb i').1 _).unique (crd_spec _ i') ?_` and prove the remaining obligations. Introduce `j`. Rewrite using `[hz j]`. Use `symm`.

Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Rewrite using `[constBF_eq]`. Simplify using `[resTop]`. Establish `hne : (i', c') ≠ (i, c)` using `fun h => hi (Prod.ext_iff.1 h).1`. Rewrite using `[h1]`.

Simplify using `[hne]`. Establish `hπ : v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)) = ((1 : ℚ) : WithTop ℚ)`. Establish `h1` using `hv (algebraMap V (FractionRing V) ϖ) 1 ⟨1, by simp⟩`. Simplify using `using h1`. Set `q : Fin (k ^ Module.finrank ℤ D.toPre.X) × Fin (k ^ D.toPre.P.g) → ℚ` to `fun p => 0 + (Q (e0 p.1) : ℚ) / k`.

Establish `ht` using `fun p => GlobalTheory.ValuedPrincipal.main F v _ hπ hF (q p)`. Establish `hP : ∀ s, NuGe D Q F v k s 0 ↔ ∀ p, ((q p : ℚ) : WithTop ℚ) ≤ v (φ s p)`. Introduce `s`. Establish `hS : ∀ χ : D.toPre.X, ∃ α ∈ Finset.univ.image e0, ∃ m0, χ = α + k • m0`. Introduce `χ`.

Take `⟨i, hi, -⟩` from `he0 χ`. Conclude with `⟨e0 i, Finset.mem_image_of_mem _ (Finset.mem_univ _), hi⟩`. Rewrite using `[n1a V ϖ hϖ D Q hQ F v hv k hk _ hS s 0]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `h ⟨i, c⟩`.

Establish `h1` using `h (e0 i) (Finset.mem_image_of_mem _ (Finset.mem_univ _))`. Rewrite `h1` using `[(hbb i).2 _ _ (crd_spec s i)]`. Conclude with `h1 c`. Introduce `h α hα`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hα`.

Rewrite using `[(hbb i).2 _ _ (crd_spec s i)]`. Introduce `c`. Conclude with `h (i, c)`. Establish `hr : D.toPre.rank = Module.finrank ℤ D.toPre.X` using `Nat.add_zero _`. Conclude with `exists_basis_of_coord v φ hφ B hB q ht (fun s => NuGe D Q F v k s 0) hP ((finCongr (by rw [pow_add, hr])).trans finProdFinEquiv.symm)`.
-/
theorem main : GlobalFnsSt → TwistBaseChangeStatement → UUStatement := by
  classical
  intro hG hTw V _ _ _ ϖ hϖ D Q hQ F _ _ v hv hF k hk
  obtain ⟨hinj, e0, he0⟩ := GlobalTheory.exists_representatives_mod_nsmul D.toPre.X k hk
  choose bb hbb using fun i => GlobalTheory.IntegralCoord.main hTw V ϖ hϖ D F v hv k hk (e0 i)
  choose crd crd_spec using fun (s : Fam D.toPre F k) i => ((hbb i).1 (s.s (e0 i))).exists

  have hadd : ∀ (s t : Fam D.toPre F k) i, crd (s + t) i = fun c => crd s i c + crd t i c := by
    intro s t i
    refine ((hbb i).1 _).unique (crd_spec _ i) ?_
    intro j
    rw [add_f, crd_spec s i j, crd_spec t i j, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [constBF_eq, constBF_eq, constBF_eq]
    simp only [map_add, resTop, add_mul]
  have hsmul : ∀ (ζ : F) (s : Fam D.toPre F k) i, crd (ζ • s) i = fun c => ζ * crd s i c := by
    intro ζ s i
    refine ((hbb i).1 _).unique (crd_spec _ i) ?_
    intro j
    rw [smul_f, crd_spec s i j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [constBF_eq, constBF_eq]
    simp only [map_mul, resTop, _root_.mul_assoc]
  let φ : Fam D.toPre F k →ₗ[F] (Fin (k ^ Module.finrank ℤ D.toPre.X) × Fin (k ^ D.toPre.P.g) → F) :=
    { toFun := fun s p => crd s p.1 p.2
      map_add' := fun s t => by
        funext p
        simp only [hadd, Pi.add_apply]
      map_smul' := fun ζ s => by
        funext p
        simp only [hsmul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul] }

  have hφ : Function.Injective φ := by
    intro s t h
    apply fam_ext
    intro χ j
    obtain ⟨i, ⟨m, rfl⟩, -⟩ := he0 χ
    have hag : ∀ j, (s.s (e0 i)).f j = (t.s (e0 i)).f j := by
      intro j
      rw [crd_spec s i j, crd_spec t i j]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [show crd s i c = crd t i c from congrFun h (i, c)]
    exact GlobalTheory.fam_eq_on_class_of_eq hG V D.toPre F k s t (e0 i) hag m j

  have hcls : ∀ i (a b : D.toPre.X), e0 i + k • a = e0 i + k • b → a = b :=
    fun i a b h => hinj a b (add_left_cancel h)
  choose B hB1 hB2 using fun p : Fin (k ^ Module.finrank ℤ D.toPre.X) × Fin (k ^ D.toPre.P.g) =>
    ReciprocityTheory.ChartRestriction.G.DVR.UUA.exists_fam_rep hG D.tau_bimult k (e0 p.1) (hcls p.1) (bb p.1 p.2)
  have hB : ∀ p, φ (B p) = Pi.single p 1 := by
    rintro ⟨i, c⟩
    funext ⟨i', c'⟩
    show crd (B (i, c)) i' c' = _
    by_cases hi : i' = i
    · subst hi
      have h1 : crd (B (i', c)) i' = Pi.single c 1 := by
        refine ((hbb i').1 _).unique (crd_spec _ i') ?_
        intro j
        rw [hB1, Finset.sum_eq_single c]
        · rw [constBF_eq]
          simp [resTop]
        · intro b _ hb
          rw [constBF_eq]
          simp [resTop, hb]
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [h1]
      by_cases hc : c' = c
      · subst hc
        simp
      · have hne : (i', c') ≠ (i', c) := fun h => hc (Prod.ext_iff.1 h).2
        simp [hc, hne]
    · have hz : ∀ j, ((B (i, c)).s (e0 i')).f j = 0 := by
        refine hB2 (i, c) (e0 i') fun mu h => hi ?_
        exact ((he0 (e0 i')).unique ⟨0, by simp⟩ ⟨mu, h.symm⟩)
      have h1 : crd (B (i, c)) i' = 0 := by
        refine ((hbb i').1 _).unique (crd_spec _ i') ?_
        intro j
        rw [hz j]
        symm
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [constBF_eq]
        simp [resTop]
      have hne : (i', c') ≠ (i, c) := fun h => hi (Prod.ext_iff.1 h).1
      rw [h1]
      simp [hne]

  have hπ : v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)) = ((1 : ℚ) : WithTop ℚ) := by
    have h1 := hv (algebraMap V (FractionRing V) ϖ) 1 ⟨1, by simp⟩
    simpa using h1
  let q : Fin (k ^ Module.finrank ℤ D.toPre.X) × Fin (k ^ D.toPre.P.g) → ℚ :=
    fun p => 0 + (Q (e0 p.1) : ℚ) / k
  have ht := fun p => GlobalTheory.ValuedPrincipal.main F v _ hπ hF (q p)

  have hP : ∀ s, NuGe D Q F v k s 0 ↔ ∀ p, ((q p : ℚ) : WithTop ℚ) ≤ v (φ s p) := by
    intro s
    have hS : ∀ χ : D.toPre.X, ∃ α ∈ Finset.univ.image e0, ∃ m0, χ = α + k • m0 := by
      intro χ
      obtain ⟨i, hi, -⟩ := he0 χ
      exact ⟨e0 i, Finset.mem_image_of_mem _ (Finset.mem_univ _), hi⟩
    rw [n1a V ϖ hϖ D Q hQ F v hv k hk _ hS s 0]
    constructor
    · rintro h ⟨i, c⟩
      have h1 := h (e0 i) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      rw [(hbb i).2 _ _ (crd_spec s i)] at h1
      exact h1 c
    · intro h α hα
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hα
      rw [(hbb i).2 _ _ (crd_spec s i)]
      intro c
      exact h (i, c)
  have hr : D.toPre.rank = Module.finrank ℤ D.toPre.X := Nat.add_zero _
  exact exists_basis_of_coord v φ hφ B hB q ht (fun s => NuGe D Q F v k s 0) hP
    ((finCongr (by rw [pow_add, hr])).trans finProdFinEquiv.symm)

end GlobalTheory.UnitBallFree
