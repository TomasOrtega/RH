import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SumDivHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DirOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EPrim
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EigAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ChebQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
import Mathlib.Topology.Algebra.ClopenNhdofOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published

namespace UpperTheory.V.Sd.PadicNormCongruences

section Norm

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Use `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x - 1) (y := 1) (by rw [norm_one]; exact h.ne)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, norm_one, max_eq_right h.le]`. Then use the resulting hypothesis.
-/
private theorem norm_eq_one_of {x : Qbar l} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x - 1) (y := 1) (by rw [norm_one]; exact h.ne)
  rwa [sub_add_cancel, norm_one, max_eq_right h.le] at this

/- English proof (translation)
The claim follows from `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)`.
-/
private theorem small_add {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)

/- English proof (translation)
Establish `h2 : ‖x‖ ^ n = 1` using `by rw [← norm_pow, h, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2`.
-/
private theorem norm_root {x : Qbar l} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : ‖x‖ = 1 := by
  have h2 : ‖x‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2

/- English proof (translation)
Establish `h : (l : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l])` using `by simp`. Rewrite using `[h, norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`.
-/
private theorem norm_l : ‖(l : Qbar l)‖ < 1 := by
  have h : (l : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

/- English proof (translation)
Establish `hx` using `norm_root hl.out.ne_zero h`. Establish `hy : ‖x - 1‖ ≤ 1`. Rewrite using `[sub_eq_add_neg]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (by simp [hx])`. Establish `e` using `add_pow_prime_eq hl.out (x - 1) 1`.

Rewrite `e` using `[sub_add_cancel, h, one_pow]`. Use `set S := ∑ k ∈ Finset.Ioo 0 l, (x - 1) ^ (k - 1) * 1 ^ (l - k - 1) * ((l.choose k / l : ℕ) : Qbar l) with hS`. Establish `hs : ‖S‖ ≤ 1`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_` and prove the remaining obligations. Rewrite using `[one_pow, mul_one, norm_mul, norm_pow]`.

Conclude with `mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hy) (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)`. Establish `e2 : (x - 1) ^ l = -((l : Qbar l) * ((x - 1) * S))` using `by linear_combination -e`. Establish `h3 : ‖x - 1‖ ^ l < 1`. Rewrite using `[← norm_pow, e2, norm_neg, norm_mul, norm_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) norm_l (mul_le_one₀ hy (norm_nonneg _) hs)`.

Conclude with `(pow_lt_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h3`.
-/
private theorem root_small {x : Qbar l} (h : x ^ l = 1) : ‖x - 1‖ < 1 := by
  have hx := norm_root hl.out.ne_zero h
  have hy : ‖x - 1‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (by simp [hx])
  have e := add_pow_prime_eq hl.out (x - 1) 1
  rw [sub_add_cancel, h, one_pow] at e
  set S := ∑ k ∈ Finset.Ioo 0 l, (x - 1) ^ (k - 1) * 1 ^ (l - k - 1) * ((l.choose k / l : ℕ) : Qbar l) with hS
  have hs : ‖S‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [one_pow, mul_one, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hy) (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
  have e2 : (x - 1) ^ l = -((l : Qbar l) * ((x - 1) * S)) := by linear_combination -e
  have h3 : ‖x - 1‖ ^ l < 1 := by
    rw [← norm_pow, e2, norm_neg, norm_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) norm_l (mul_le_one₀ hy (norm_nonneg _) hs)
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h3

variable (l) in

private def U : Subgroup (Qbar l)ˣ where
  carrier := {u | ‖(u : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    have e : ((u * v : (Qbar l)ˣ) : Qbar l) - 1 = u * (v - 1) + (u - 1) := by push_cast; ring
    show ‖_‖ < 1
    rw [e]
    refine small_add ?_ hu
    rw [norm_mul, norm_eq_one_of hu, one_mul]
    exact hv
  inv_mem' {u} hu := by
    have e : (u : Qbar l) * (((u⁻¹ : (Qbar l)ˣ) : Qbar l) - 1) = -(u - 1) := by rw [mul_sub, Units.mul_inv]; ring
    have := congrArg norm e
    rw [norm_mul, norm_eq_one_of hu, one_mul, norm_neg] at this
    show ‖_‖ < 1
    rw [this]
    exact hu

/- English proof (translation)
Establish `e : ((a * u : (Qbar l)ˣ) : Qbar l) - a = a * (u - 1)` using `by push_cast; ring`. Unfold `Cong`. Rewrite using `[e, norm_mul, ha, one_mul]`. Conclude with `hu`.
-/
private theorem cong_mul {a u : (Qbar l)ˣ} (ha : ‖(a : Qbar l)‖ = 1) (hu : u ∈ U l) : Cong (a * u) a := by
  have e : ((a * u : (Qbar l)ˣ) : Qbar l) - a = a * (u - 1) := by push_cast; ring
  unfold Cong
  rw [e, norm_mul, ha, one_mul]
  exact hu

/- English proof (translation)
Use `(IsUltrametricDist.isClosed_ball (0 : Qbar l) 1).preimage hf` as an intermediate fact. Simplify `this` using `[Set.preimage]`.
-/
private theorem isClosed_small {Γ : Type} [TopologicalSpace Γ] {f : Γ → Qbar l} (hf : Continuous f) :
    IsClosed {s | ‖f s‖ < 1} := by
  have := (IsUltrametricDist.isClosed_ball (0 : Qbar l) 1).preimage hf
  simpa [Set.preimage] using this

/- English proof (translation)
Introduce `s i`. Establish `e : (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly - ∏ j, (X - C ((![1, Φ] j s : (Qbar l)ˣ) : Qbar l)) = C (-((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + Φ s))) * X + C ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det - Φ s)`. Rewrite using `[Matrix.charpoly_fin_two, Fin.prod_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.one_apply, Units.val_one, map_one, map_neg, map_sub, map_add]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← coeff_sub, e, coeff_add, coeff_C_mul_X, coeff_C]`. Use `small_add ?_ ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[norm_neg]`. Conclude with `ht s`.

Simplify using the standard rewrite rules. Use `split_ifs`. Conclude with `hd s`. Simplify using the standard rewrite rules.
-/
private theorem resSum_of {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)) (Φ : Γ →* (Qbar l)ˣ)
    (ht : ∀ s, ‖(ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + Φ s)‖ < 1)
    (hd : ∀ s, ‖(ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det - Φ s‖ < 1) : ResSum ρ ![1, Φ] := by
  intro s i
  have e : (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly - ∏ j, (X - C ((![1, Φ] j s : (Qbar l)ˣ) : Qbar l)) =
      C (-((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + Φ s))) * X +
        C ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det - Φ s) := by
    rw [Matrix.charpoly_fin_two, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.one_apply, Units.val_one, map_one, map_neg, map_sub, map_add]
    ring
  rw [← coeff_sub, e, coeff_add, coeff_C_mul_X, coeff_C]
  refine small_add ?_ ?_
  · split_ifs
    · rw [norm_neg]; exact ht s
    · simp
  · split_ifs
    · exact hd s
    · simp

/- English proof (translation)
Rewrite `h` using `[Matrix.charpoly_fin_two]`. Establish `h0` using `congrArg (coeff · 0) h`. Establish `h1` using `congrArg (coeff · 1) h`. Simplify using `[coeff_X, coeff_C, coeff_X_pow] at h0 h1`. Conclude with `⟨by rw [← h1]; simp, by rw [← h0]; simp⟩`.
-/
private theorem tr_det (ι : Qbar l ≃+* ℂ) (B : Matrix (Fin 2) (Fin 2) (Qbar l)) {a d : ℂ}
    (h : B.charpoly.map ι.toRingHom = X ^ 2 - C a * X + C d) : B.trace = ι.symm a ∧ B.det = ι.symm d := by
  rw [Matrix.charpoly_fin_two] at h
  have h0 := congrArg (coeff · 0) h
  have h1 := congrArg (coeff · 1) h
  simp [coeff_X, coeff_C, coeff_X_pow] at h0 h1
  exact ⟨by rw [← h1]; simp, by rw [← h0]; simp⟩

end Norm

section Gal

variable {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

/- English proof (translation)
The claim follows from `(ML.placeBasic Ω).2.2.2.1 A v M ((Nat.Prime.coprime_iff_not_dvd hv).2 hM) hA`.
-/
private theorem not_over {A : ValuationSubring Ω} {v M : ℕ} (hv : v.Prime) (hA : A.valuation (v : Ω) < 1) (hM : ¬ v ∣ M) :
    ¬ A.valuation (M : Ω) < 1 :=
  (ML.placeBasic Ω).2.2.2.1 A v M ((Nat.Prime.coprime_iff_not_dvd hv).2 hM) hA

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dirG_val {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) (s : G ℚ Ω) :
    (Chr.dirG ℚ Ω χ s : O) = χ (Chr.cls ℚ Ω N s : ZMod N) := rfl

/- English proof (translation)
Establish `h : IsLocallyConstant (Chr.cls ℚ Ω N)`. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Use `fun x => ⟨_, (Chr.clsFacts ℚ Ω N).1.preimage (continuous_const_mul x⁻¹), by simp, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1 : Chr.cls ℚ Ω N (x⁻¹ * y) = 1` using `hy`. Rewrite `h1` using `[map_mul, map_inv, inv_mul_eq_one]`.

Conclude with `h1.symm`. Conclude with `(h.comp fun u : (ZMod N)ˣ => χ (u : ZMod N)).continuous`.
-/
private theorem dirG_cont {N : ℕ} [NeZero N] (χ : DirichletCharacter (Qbar l) N) :
    Continuous fun s : G ℚ Ω => (Chr.dirG ℚ Ω χ s : Qbar l) := by
  have h : IsLocallyConstant (Chr.cls ℚ Ω N) := by
    rw [IsLocallyConstant.iff_exists_open]
    refine fun x => ⟨_, (Chr.clsFacts ℚ Ω N).1.preimage (continuous_const_mul x⁻¹), by simp, fun y hy => ?_⟩
    have h1 : Chr.cls ℚ Ω N (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  exact (h.comp fun u : (ZMod N)ˣ => χ (u : ZMod N)).continuous

/- English proof (translation)
Use `norm_root (n := Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_` and prove the remaining obligations. Rewrite using `[dirG_val, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]`.
-/
private theorem dirG_norm {N : ℕ} [NeZero N] (χ : DirichletCharacter (Qbar l) N) (s : G ℚ Ω) :
    ‖(Chr.dirG ℚ Ω χ s : Qbar l)‖ = 1 := by
  refine norm_root (n := Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_
  rw [dirG_val, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]

/- English proof (translation)
Rewrite using `[Chr.dirG, MonoidHom.comp_apply, MonoidHom.mem_ker.1 ((Chr.clsFacts ℚ Ω N).2.2.2.2 A hA hg), map_one]`.
-/
private theorem dirG_unr {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {A : ValuationSubring Ω}
    (hA : ¬ A.valuation (N : Ω) < 1) {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) : Chr.dirG ℚ Ω χ g = 1 := by
  rw [Chr.dirG, MonoidHom.comp_apply, MonoidHom.mem_ker.1 ((Chr.clsFacts ℚ Ω N).2.2.2.2 A hA hg), map_one]

/- English proof (translation)
Establish `h2` using `(Chr.clsFacts ℚ Ω N).2.2.1 σ (ZMod.unitOfCoprime v hc) fun ζ hζ => by`. Rewrite using `[h1 ζ hζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod v hζ]`. Rewrite using `[h2, ZMod.coe_unitOfCoprime]`.
-/
private theorem cls_pow {N v : ℕ} [NeZero N] (hc : v.Coprime N) {σ : G ℚ Ω} (h1 : ∀ ζ : Ω, ζ ^ N = 1 → σ ζ = ζ ^ v) :
    ((Chr.cls ℚ Ω N σ : (ZMod N)ˣ) : ZMod N) = v := by
  have h2 := (Chr.clsFacts ℚ Ω N).2.2.1 σ (ZMod.unitOfCoprime v hc) fun ζ hζ => by
    rw [h1 ζ hζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod v hζ]
  rw [h2, ZMod.coe_unitOfCoprime]

/- English proof (translation)
Rewrite using `[dirG_val, cls_pow ((Nat.Prime.coprime_iff_not_dvd hv).2 hN) ((ML.placeBasic Ω).2.2.2.2.2.2.1 A v N σ h (not_over hv hA hN))]`.
-/
private theorem dirG_frob {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {A : ValuationSubring Ω} {v : ℕ}
    (hv : v.Prime) (hA : A.valuation (v : Ω) < 1) (hN : ¬ v ∣ N) {σ : G ℚ Ω} (h : IsFrob (F := ℚ) A v σ) :
    (Chr.dirG ℚ Ω χ σ : O) = χ v := by
  rw [dirG_val, cls_pow ((Nat.Prime.coprime_iff_not_dvd hv).2 hN)
    ((ML.placeBasic Ω).2.2.2.2.2.2.1 A v N σ h (not_over hv hA hN))]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem cyc_val (s : G ℚ Ω) : (cycBar ℚ Ω l s : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := rfl

/- English proof (translation)
The claim follows from `(continuous_algebraMap ℚ_[l] (Qbar l)).comp (continuous_subtype_val.comp ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l)))`.
-/
private theorem cyc_cont : Continuous fun s : G ℚ Ω => (cycBar ℚ Ω l s : Qbar l) :=
  (continuous_algebraMap ℚ_[l] (Qbar l)).comp
    (continuous_subtype_val.comp ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l)))

/- English proof (translation)
Rewrite using `[cyc_val, norm_algebraMap']`. Conclude with `PadicInt.norm_units _`.
-/
private theorem cyc_norm (s : G ℚ Ω) : ‖(cycBar ℚ Ω l s : Qbar l)‖ = 1 := by
  rw [cyc_val, norm_algebraMap']
  exact PadicInt.norm_units _

/- English proof (translation)
Take `⟨w, hw, rfl, -⟩` from `(ML.placeBasic Ω).2.2.2.2.2.2.2.2.1 A v hv hA`. Establish `h1 : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal` using `fun h' => not_over hv hA hN (by simpa using (hw _).2 h')`. Rewrite using `[cyc_val, cycZ_of_isFrob h1 hw h]`. Simplify using the standard rewrite rules.
-/
private theorem cyc_frob {A : ValuationSubring Ω} {v : ℕ} (hv : v.Prime) (hA : A.valuation (v : Ω) < 1) (hN : ¬ v ∣ l)
    {σ : G ℚ Ω} (h : IsFrob (F := ℚ) A v σ) : (cycBar ℚ Ω l σ : Qbar l) = v := by
  obtain ⟨w, hw, rfl, -⟩ := (ML.placeBasic Ω).2.2.2.2.2.2.2.2.1 A v hv hA
  have h1 : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h' => not_over hv hA hN (by simpa using (hw _).2 h')
  rw [cyc_val, cycZ_of_isFrob h1 hw h]
  simp

/- English proof (translation)
Assume the negation of the conclusion as `hs`. Take `⟨q, A, σ, hq, hqT, hA, hσ, hV⟩` from `ML.chebQ Ω _ hP.isOpen_compl ⟨s, hs⟩ T hT`. Conclude with `hV (h q A σ hq hqT hA hσ)`.
-/
private theorem of_frob {P : G ℚ Ω → Prop} (hP : IsClosed {s | P s}) {T : ℕ} (hT : T ≠ 0)
    (h : ∀ (q : ℕ) (A : ValuationSubring Ω) (σ : G ℚ Ω), q.Prime → ¬ q ∣ T → A.valuation (q : Ω) < 1 → IsFrob (F := ℚ) A q σ → P σ)
    (s : G ℚ Ω) : P s := by
  by_contra hs
  obtain ⟨q, A, σ, hq, hqT, hA, hσ, hV⟩ := ML.chebQ Ω _ hP.isOpen_compl ⟨s, hs⟩ T hT
  exact hV (h q A σ hq hqT hA hσ)

/- English proof (translation)
Use `haveI : IsGalois ℚ Ω := {}`. Establish `key` using `ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω) ⟨K.topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩`. Use `le_trans (le_sInf ?_) key.ge` and prove the remaining obligations. Introduce and unpack `N ⟨hNo, hN⟩`. Establish `h` using `(Subgroup.le_topologicalClosure _).trans hN`.

Conclude with `Kum.decGen ℚ Ω A _ γ N hv hγ hNo (hI.trans h) (h hK)`.
-/
private theorem dec_le {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceOver A v) {γ : G ℚ Ω}
    (hγ : IsFrob A (normV v) γ) (K : Subgroup (G ℚ Ω)) (hI : Ine (F := ℚ) A ≤ K) (hK : γ ∈ K) :
    Dec (F := ℚ) A ≤ K.topologicalClosure := by
  haveI : IsGalois ℚ Ω := {}
  have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω) ⟨K.topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
  refine le_trans (le_sInf ?_) key.ge
  rintro N ⟨hNo, hN⟩
  have h := (Subgroup.le_topologicalClosure _).trans hN
  exact Kum.decGen ℚ Ω A _ γ N hv hγ hNo (hI.trans h) (h hK)

/- English proof (translation)
Establish `hq : normV v = Ideal.absNorm v.asIdeal`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression. Rewrite using `[hq]`. Conclude with `⟨fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), Ideal.absNorm_mem _⟩`.
-/
private theorem normV_mem (v : HeightOneSpectrum (𝓞 ℚ)) : normV v ≠ 0 ∧ ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have hq : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  rw [hq]
  exact ⟨fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), Ideal.absNorm_mem _⟩

/- English proof (translation)
Establish `h0 : Ideal.span {(a : 𝓞 ℚ)} ≠ 0` using `by simpa using h`. Use `Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)` and prove the remaining obligations. Take `⟨c, rfl⟩` from `not_not.1 hw`. Use `Ideal.dvd_span_singleton.2 ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_mul]`.

Conclude with `Ideal.mul_mem_right _ _ (normV_mem w).2`.
-/
private theorem ev_not_dvd {a : ℕ} (h : a ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ¬ normV w ∣ a := by
  have h0 : Ideal.span {(a : 𝓞 ℚ)} ≠ 0 := by simpa using h
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  obtain ⟨c, rfl⟩ := not_not.1 hw
  refine Ideal.dvd_span_singleton.2 ?_
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (normV_mem w).2

/- English proof (translation)
Use `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`. Take `⟨v, hv⟩` from `(places ℚ Ω 2 A).1 hA`. Take `⟨p, hp, h⟩` from `((Chr.placesQ Ω).2.1 A _ (normV_mem v).1).1 (by simpa using (hv _).2 (normV_mem v).2)`. Conclude with `⟨p, Nat.prime_of_mem_primeFactors hp, h⟩`.
-/
private theorem exists_prime (A : ValuationSubring Ω) (hA : A ≠ ⊤) : ∃ q : ℕ, q.Prime ∧ A.valuation (q : Ω) < 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv⟩ := (places ℚ Ω 2 A).1 hA
  obtain ⟨p, hp, h⟩ := ((Chr.placesQ Ω).2.1 A _ (normV_mem v).1).1 (by simpa using (hv _).2 (normV_mem v).2)
  exact ⟨p, Nat.prime_of_mem_primeFactors hp, h⟩

/- English proof (translation)
Take `⟨g, hg⟩` from `hκ`. Prove the components needed by the constructor for the conclusion. Establish `e : Matrix.GeneralLinearGroup.det (g * ρ s * g⁻¹) = Matrix.GeneralLinearGroup.det (ρ s)`. Rewrite using `[map_mul, map_mul, map_inv, mul_inv_cancel_comm]`. Rewrite using `[← e]`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, (hg s).1 1 0 (by decide), (hg s).2, (hg s).2]`. Simplify using the standard rewrite rules. Take `⟨γ, hγ⟩` from `exists_isFrob hv`. Establish `h1` using `dec_le hv hγ (((U l).comap (κ 1)).map (Dec (F := ℚ) A).subtype) (fun t ht => ⟨⟨t, ht.1⟩, by show κ 1 _ ∈ U l`.

Rewrite using `[hI _ ht]`. Conclude with `one_mem _, rfl⟩)`. Use the proof step `⟨⟨γ, hγ.1⟩, hF _ hγ, rfl⟩ s.2`. Establish `hc : Continuous fun t : G ℚ Ω => (g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 1 1 - 1` using `((continuous_apply 1).comp ((continuous_apply 1).comp ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (Qbar l))).comp ((continuous_const.mul hρ).mul continuous_const)))).sub continuous_const`. Establish `h2` using `closure_minimal (t := {t : G ℚ Ω | ‖(g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 1 1 - 1‖ < 1}) (by`.

Introduce and unpack `_ ⟨t, ht, rfl⟩`. Use `show ‖(g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 1 1 - 1‖ < 1`. Rewrite using `[(hg t).2]`. Conclude with `ht) (isClosed_small hc) h1`. Use `show ‖_‖ < 1`.

Rewrite using `[← (hg s).2]`. Conclude with `h2`.
-/
private theorem above_of {ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)} (hρ : Continuous ρ) {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceOver A v) {κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ}
    (hκ : IsFlagOn ρ (Dec (F := ℚ) A) κ) (hI : ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 1 s = 1)
    (hF : ∀ σ : ↥(Dec (F := ℚ) A), IsFrob A (normV v) (σ : G ℚ Ω) → κ 1 σ ∈ U l) (s : ↥(Dec (F := ℚ) A)) :
    κ 0 s * κ 1 s = Matrix.GeneralLinearGroup.det (ρ s) ∧ κ 1 s ∈ U l := by
  obtain ⟨g, hg⟩ := hκ
  constructor
  · have e : Matrix.GeneralLinearGroup.det (g * ρ s * g⁻¹) = Matrix.GeneralLinearGroup.det (ρ s) := by
      rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [← e]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, (hg s).1 1 0 (by decide), (hg s).2, (hg s).2]
    simp
  · obtain ⟨γ, hγ⟩ := exists_isFrob hv
    have h1 := dec_le hv hγ (((U l).comap (κ 1)).map (Dec (F := ℚ) A).subtype)
      (fun t ht => ⟨⟨t, ht.1⟩, by
        show κ 1 _ ∈ U l
        rw [hI _ ht]; exact one_mem _, rfl⟩)
      ⟨⟨γ, hγ.1⟩, hF _ hγ, rfl⟩ s.2
    have hc : Continuous fun t : G ℚ Ω => (g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 1 1 - 1 :=
      ((continuous_apply 1).comp ((continuous_apply 1).comp
        ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (Qbar l))).comp ((continuous_const.mul hρ).mul continuous_const)))).sub continuous_const
    have h2 := closure_minimal (t := {t : G ℚ Ω | ‖(g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 1 1 - 1‖ < 1}) (by
      rintro _ ⟨t, ht, rfl⟩
      show ‖(g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 1 1 - 1‖ < 1
      rw [(hg t).2]
      exact ht) (isClosed_small hc) h1
    show ‖_‖ < 1
    rw [← (hg s).2]
    exact h2

/- English proof (translation)
Take `⟨ρ, hc, hi, H⟩` from `P.hida k N hk χ g l Ω ι`. Establish `hlN : l * N ≠ 0` using `mul_ne_zero hl.out.ne_zero (NeZero.ne N)`. Establish `pl` using `(ML.placeBasic Ω).2.2.2.2.2.2.2.2.1`. Establish `hθU : ∀ s, θ s ∈ U l` using `fun s => root_small (by`. Use `DFunLike.congr_fun hθ s` as an intermediate fact.

Rewrite `this` using `[MonoidHom.pow_apply]`. Rewrite using `[← Units.val_pow_eq_pow_val, this]`. Use the proof step `rfl)`. Use `set D : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * (φ * θ) with hD`. Use `set Φ : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * φ with hΦ`.

Establish `hDv : ∀ s, (D s : Qbar l) = (cycBar ℚ Ω l s : Qbar l) ^ (k - 1) * Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) s` using `fun s => by`. Rewrite using `[hD, ← hm]`. Simplify using the standard rewrite rules. Establish `hDΦ : ∀ s, D s = Φ s * θ s` using `fun s => by simp [hD, hΦ, mul_assoc]`. Establish `hΦn : ∀ s, ‖(Φ s : Qbar l)‖ = 1` using `fun s => by`.

Use `congrArg norm (hDv s)` as an intermediate fact. Rewrite `this` using `[norm_mul, norm_pow, cyc_norm, dirG_norm, one_pow, mul_one, hDΦ, Units.val_mul, norm_mul, norm_eq_one_of (hθU s), mul_one]`. Then use the resulting hypothesis. Establish `hDc : Continuous fun s => (D s : Qbar l)`. Simplify using `only [hDv]`. Conclude with `(cyc_cont.pow _).mul (dirG_cont _)`.

Establish `hρc : Continuous fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l))` using `Units.continuous_val.comp hc`. Establish `hF : ∀ (q : ℕ) (A : ValuationSubring Ω) (σ : G ℚ Ω), q.Prime → ¬ q ∣ l * N → A.valuation (q : Ω) < 1 → IsFrob (F` using `ℚ) A q σ → ‖(ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + D σ)‖ < 1 ∧ (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = D σ := by`. Introduce `q A σ hq hqT hA hσ`. Establish `h1 : (D σ : Qbar l) = ι.symm (χ (q : ZMod N) * (q : ℂ) ^ (k - 1))`. Rewrite using `[hDv, cyc_frob hq hA (fun h => hqT (h.mul_right _)) hσ, dirG_frob _ hq hA (fun h => hqT (h.mul_left _)) hσ]`.

Simplify using `[mul_comm]`. Take `⟨w, hw, rfl, -⟩` from `pl A q hq hA`. Take `⟨ht, hd⟩` from `tr_det ι _ (((H w A hw).1 hqT).2 σ hσ)`. Rewrite using `[ht, hd, h1]`. Use `⟨?_, rfl⟩` and prove the remaining obligations.

Use `hg _ hq` as an intermediate fact. Rewrite `this` using `[map_sub, map_add, map_one]`. Then use the resulting hypothesis. Establish `hdet : ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = D s` using `of_frob (isClosed_eq hρc.matrix_det hDc) hlN fun q A σ a b c d => (hF q A σ a b c d).2`. Establish `hdet' : ∀ s, Matrix.GeneralLinearGroup.det (ρ s) = D s` using `fun s => Units.ext (hdet s)`. Establish `htr : ∀ s, ‖(ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + D s)‖ < 1` using `of_frob (isClosed_small (hρc.matrix_trace.sub (continuous_const.add hDc))) hlN fun q A σ a b c d => (hF q A σ a b c d).1`.

Establish `hcong : ∀ s, ‖(D s : Qbar l) - Φ s‖ < 1` using `fun s => by`. Rewrite using `[hDΦ]`. Conclude with `cong_mul (hΦn s) (hθU s)`. Use `⟨ρ, hc, hi, eigAut P k N hk χ hχ g l Ω ι ρ hc hi ((ev_not_dvd hlN).mono fun w hw A hA => (H w A hA).1 hw), MonoidHom.ext hdet', resSum_of ρ Φ (fun s => ?_) fun s => ?_, fun A hA => ?_, fun A hA => ?_⟩` and prove the remaining obligations. Use `small_add (htr s) (hcong s)` as an intermediate fact.

Use `this using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hdet]`. Conclude with `hcong s`. Rewrite using `[← hm]`.

Distinguish the cases in `hAN : A.valuation (N : Ω) < 1`. Take `⟨q, hq, hqA⟩` from `((Chr.placesQ Ω).2.1 A N (NeZero.ne N)).1 hAN`. Take `⟨w, hw, rfl, -⟩` from `pl A q (Nat.prime_of_mem_primeFactors hq) hqA`. Conclude with `(H w A hw).2.2 (fun h => hA (h ▸ hqA)) (Nat.dvd_of_mem_primeFactors hq) (by rw [show χ.conductor = N from hχ])`. Establish `h1 : ∀ s ∈ Ine (F` using `ℚ) A, ρ s = 1 := by`.

Distinguish the cases in `hT : A = ⊤`. Introduce `s hs`. Rewrite `hs` using `[((places ℚ Ω l A).2.1 hT).1, Subgroup.mem_bot]`. Rewrite using `[hs, map_one]`. Take `⟨q, hq, hqA⟩` from `exists_prime A hT`.

Take `⟨w, hw, rfl, -⟩` from `pl A q hq hqA`. Use `((H w A hw).1 ?_).1` and prove the remaining obligations. Introduce and unpack `⟨c, hc⟩`. Establish `h2 : A.valuation ((l * N : ℕ) : Ω) < 1`. Rewrite using `[hc]`.

Conclude with `((ML.placeBasic Ω).2.2.1 A _ _).2 (Or.inl hqA)`. Conclude with `(((ML.placeBasic Ω).2.2.1 A _ _).1 h2).elim hA hAN`. Use `⟨1, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[h1 s hs]`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dirG_unr _ hAN hs]`. Take `⟨w, hw, hwl, -⟩` from `pl A l hl.out hA`. Establish `hAN` using `not_over hl.out hA hN`. Establish `hs : ‖ι.symm (χ (l : ZMod N) * (l : ℂ) ^ (k - 1))‖ < 1`. Take `⟨γ, hγ⟩` from `exists_isFrob hw`.

Rewrite `hγ` using `[hwl]`. Establish `h1` using `dirG_norm (χ.ringHomComp ι.symm.toRingHom) γ`. Rewrite `h1` using `[dirG_frob _ hl.out hA hN hγ]`. Establish `h2 : ‖ι.symm (χ (l : ZMod N))‖ = 1` using `h1`. Rewrite using `[map_mul, norm_mul, h2, one_mul, map_pow, map_natCast, norm_pow]`.

Conclude with `pow_lt_one₀ (norm_nonneg _) norm_l (by omega)`. Establish `ha : ‖ι.symm (g.a l) - 1‖ < 1`. Use `small_add (hg l hl.out) hs` as an intermediate fact. Rewrite `this` using `[← map_add]`. Rewrite using `[← map_one ι.symm, ← map_sub]`.

Use `this using 3` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Take `⟨κ, hκ, hI, hFr⟩` from `(H w A hw).2.1 hwl (norm_eq_one_of ha)`. Establish `key` using `above_of hc hw hκ hI (fun σ hσ => by`. Take `⟨h1, h2⟩` from `hFr σ (hwl ▸ hσ)`.

Establish `h3` using `congrArg ι.symm h2`. Rewrite `h3` using `[map_add, map_sub, map_mul, map_pow, RingEquiv.symm_apply_apply, map_zero]`. Establish `h4 : (κ 1 σ : Qbar l) * (κ 1 σ - ι.symm (g.a l)) = -ι.symm (χ (l : ZMod N) * (l : ℂ) ^ (k - 1))`. Take the linear combination `h3`. Establish `h5` using `congrArg norm h4`.

Rewrite `h5` using `[norm_mul, h1, one_mul, norm_neg]`. Establish `h6` using `small_add (h5.trans_lt hs) ha`. Rewrite `h6` using `[sub_add_sub_cancel]`. Conclude with `h6)`. Use `⟨κ, hκ, fun i s hs => ?_, fun i s => ?_⟩` and prove the remaining obligations.

Use `fin_cases i`. Establish `h1` using `(key s).1`. Establish `h2 : (φ * θ) s = 1` using `hm ▸ dirG_unr _ hAN hs`. Rewrite `h1` using `[hI s hs, mul_one, hdet', hD, MonoidHom.mul_apply, h2, mul_one, MonoidHom.pow_apply]`. Establish `h3 : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ)` using `by omega`.

Use `show κ 0 s = cycBar ℚ Ω l s ^ ((k : ℤ) - 1)`. Rewrite using `[h1, h3, zpow_natCast]`. Use `show κ 1 s = cycBar ℚ Ω l s ^ (0 : ℤ)`. Rewrite using `[hI s hs, zpow_zero]`. Use `fin_cases i`.

Establish `h1 : κ 0 s = Φ s * (θ s * (κ 1 s)⁻¹)`. Rewrite using `[← mul_assoc, ← hDΦ, ← hdet', ← (key s).1, mul_inv_cancel_right]`. Use `show Cong (κ 0 s) (Φ s)`. Rewrite using `[h1]`. Conclude with `cong_mul (hΦn s) (mul_mem (hθU s) (inv_mem (key s).2))`.

Conclude with `(key s).2`.
-/
private theorem core (P : Hypotheses₂) (ι : Qbar l ≃+* ℂ) {k N : ℕ} [NeZero N] (hk : 2 ≤ k) (hN : ¬ l ∣ N) {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (g : Eigenform k N χ)
    (hg : ∀ p : ℕ, p.Prime → ‖ι.symm (g.a p - (1 + χ (p : ZMod N) * (p : ℂ) ^ (k - 1)))‖ < 1)
    {φ θ : G ℚ Ω →* (Qbar l)ˣ} (hm : Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) = φ * θ) (hθ : θ ^ l = 1) :
    ∃ ρ, EisRep ι φ θ k ρ := by
  obtain ⟨ρ, hc, hi, H⟩ := P.hida k N hk χ g l Ω ι
  have hlN : l * N ≠ 0 := mul_ne_zero hl.out.ne_zero (NeZero.ne N)
  have pl := (ML.placeBasic Ω).2.2.2.2.2.2.2.2.1
  have hθU : ∀ s, θ s ∈ U l := fun s => root_small (by
    have := DFunLike.congr_fun hθ s
    rw [MonoidHom.pow_apply] at this
    rw [← Units.val_pow_eq_pow_val, this]; rfl)
  set D : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * (φ * θ) with hD
  set Φ : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * φ with hΦ
  have hDv : ∀ s, (D s : Qbar l) = (cycBar ℚ Ω l s : Qbar l) ^ (k - 1) * Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) s := fun s => by
    rw [hD, ← hm]; simp
  have hDΦ : ∀ s, D s = Φ s * θ s := fun s => by simp [hD, hΦ, mul_assoc]
  have hΦn : ∀ s, ‖(Φ s : Qbar l)‖ = 1 := fun s => by
    have := congrArg norm (hDv s)
    rwa [norm_mul, norm_pow, cyc_norm, dirG_norm, one_pow, mul_one, hDΦ, Units.val_mul, norm_mul, norm_eq_one_of (hθU s), mul_one] at this
  have hDc : Continuous fun s => (D s : Qbar l) := by
    simp only [hDv]
    exact (cyc_cont.pow _).mul (dirG_cont _)
  have hρc : Continuous fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) := Units.continuous_val.comp hc
  have hF : ∀ (q : ℕ) (A : ValuationSubring Ω) (σ : G ℚ Ω), q.Prime → ¬ q ∣ l * N → A.valuation (q : Ω) < 1 → IsFrob (F := ℚ) A q σ →
      ‖(ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + D σ)‖ < 1 ∧ (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = D σ := by
    intro q A σ hq hqT hA hσ
    have h1 : (D σ : Qbar l) = ι.symm (χ (q : ZMod N) * (q : ℂ) ^ (k - 1)) := by
      rw [hDv, cyc_frob hq hA (fun h => hqT (h.mul_right _)) hσ, dirG_frob _ hq hA (fun h => hqT (h.mul_left _)) hσ]
      simp [mul_comm]
    obtain ⟨w, hw, rfl, -⟩ := pl A q hq hA
    obtain ⟨ht, hd⟩ := tr_det ι _ (((H w A hw).1 hqT).2 σ hσ)
    rw [ht, hd, h1]
    refine ⟨?_, rfl⟩
    have := hg _ hq
    rwa [map_sub, map_add, map_one] at this
  have hdet : ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = D s :=
    of_frob (isClosed_eq hρc.matrix_det hDc) hlN fun q A σ a b c d => (hF q A σ a b c d).2
  have hdet' : ∀ s, Matrix.GeneralLinearGroup.det (ρ s) = D s := fun s => Units.ext (hdet s)
  have htr : ∀ s, ‖(ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + D s)‖ < 1 :=
    of_frob (isClosed_small (hρc.matrix_trace.sub (continuous_const.add hDc))) hlN fun q A σ a b c d => (hF q A σ a b c d).1
  have hcong : ∀ s, ‖(D s : Qbar l) - Φ s‖ < 1 := fun s => by
    rw [hDΦ]; exact cong_mul (hΦn s) (hθU s)
  refine ⟨ρ, hc, hi, eigAut P k N hk χ hχ g l Ω ι ρ hc hi ((ev_not_dvd hlN).mono fun w hw A hA => (H w A hA).1 hw),
    MonoidHom.ext hdet', resSum_of ρ Φ (fun s => ?_) fun s => ?_, fun A hA => ?_, fun A hA => ?_⟩
  · have := small_add (htr s) (hcong s)
    convert this using 2
    ring
  · rw [hdet]; exact hcong s
  · rw [← hm]
    by_cases hAN : A.valuation (N : Ω) < 1
    · obtain ⟨q, hq, hqA⟩ := ((Chr.placesQ Ω).2.1 A N (NeZero.ne N)).1 hAN
      obtain ⟨w, hw, rfl, -⟩ := pl A q (Nat.prime_of_mem_primeFactors hq) hqA
      exact (H w A hw).2.2 (fun h => hA (h ▸ hqA)) (Nat.dvd_of_mem_primeFactors hq) (by rw [show χ.conductor = N from hχ])
    · have h1 : ∀ s ∈ Ine (F := ℚ) A, ρ s = 1 := by
        by_cases hT : A = ⊤
        · intro s hs
          rw [((places ℚ Ω l A).2.1 hT).1, Subgroup.mem_bot] at hs
          rw [hs, map_one]
        · obtain ⟨q, hq, hqA⟩ := exists_prime A hT
          obtain ⟨w, hw, rfl, -⟩ := pl A q hq hqA
          refine ((H w A hw).1 ?_).1
          rintro ⟨c, hc⟩
          have h2 : A.valuation ((l * N : ℕ) : Ω) < 1 := by
            rw [hc]; exact ((ML.placeBasic Ω).2.2.1 A _ _).2 (Or.inl hqA)
          exact (((ML.placeBasic Ω).2.2.1 A _ _).1 h2).elim hA hAN
      refine ⟨1, fun s hs => ?_⟩
      rw [h1 s hs]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [dirG_unr _ hAN hs]
  · obtain ⟨w, hw, hwl, -⟩ := pl A l hl.out hA
    have hAN := not_over hl.out hA hN
    have hs : ‖ι.symm (χ (l : ZMod N) * (l : ℂ) ^ (k - 1))‖ < 1 := by
      obtain ⟨γ, hγ⟩ := exists_isFrob hw
      rw [hwl] at hγ
      have h1 := dirG_norm (χ.ringHomComp ι.symm.toRingHom) γ
      rw [dirG_frob _ hl.out hA hN hγ] at h1
      have h2 : ‖ι.symm (χ (l : ZMod N))‖ = 1 := h1
      rw [map_mul, norm_mul, h2, one_mul, map_pow, map_natCast, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) norm_l (by omega)
    have ha : ‖ι.symm (g.a l) - 1‖ < 1 := by
      have := small_add (hg l hl.out) hs
      rw [← map_add] at this
      rw [← map_one ι.symm, ← map_sub]
      convert this using 3
      ring
    obtain ⟨κ, hκ, hI, hFr⟩ := (H w A hw).2.1 hwl (norm_eq_one_of ha)
    have key := above_of hc hw hκ hI (fun σ hσ => by
      obtain ⟨h1, h2⟩ := hFr σ (hwl ▸ hσ)
      have h3 := congrArg ι.symm h2
      rw [map_add, map_sub, map_mul, map_pow, RingEquiv.symm_apply_apply, map_zero] at h3
      have h4 : (κ 1 σ : Qbar l) * (κ 1 σ - ι.symm (g.a l)) = -ι.symm (χ (l : ZMod N) * (l : ℂ) ^ (k - 1)) := by
        linear_combination h3
      have h5 := congrArg norm h4
      rw [norm_mul, h1, one_mul, norm_neg] at h5
      have h6 := small_add (h5.trans_lt hs) ha
      rw [sub_add_sub_cancel] at h6
      exact h6)
    refine ⟨κ, hκ, fun i s hs => ?_, fun i s => ?_⟩
    · fin_cases i
      · have h1 := (key s).1
        have h2 : (φ * θ) s = 1 := hm ▸ dirG_unr _ hAN hs
        rw [hI s hs, mul_one, hdet', hD, MonoidHom.mul_apply, h2, mul_one, MonoidHom.pow_apply] at h1
        have h3 : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) := by omega
        show κ 0 s = cycBar ℚ Ω l s ^ ((k : ℤ) - 1)
        rw [h1, h3, zpow_natCast]
      · show κ 1 s = cycBar ℚ Ω l s ^ (0 : ℤ)
        rw [hI s hs, zpow_zero]
    · fin_cases i
      · have h1 : κ 0 s = Φ s * (θ s * (κ 1 s)⁻¹) := by
          rw [← mul_assoc, ← hDΦ, ← hdet', ← (key s).1, mul_inv_cancel_right]
        show Cong (κ 0 s) (Φ s)
        rw [h1]
        exact cong_mul (hΦn s) (mul_mem (hθU s) (inv_mem (key s).2))
      · exact (key s).2

/- English proof (translation)
Rewrite using `[dirG_val, ← (Chr.clsFacts ℚ Ω N).2.1 M h, MonoidHom.comp_apply, ZMod.unitsMap_val, ZMod.natCast_val]`.
-/
private theorem dirG_dvd {O : Type} [CommRing O] {N M : ℕ} [NeZero N] [NeZero M] (h : M ∣ N) (χ : DirichletCharacter O M) (s : G ℚ Ω) :
    (Chr.dirG ℚ Ω χ s : O) = χ ((((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N).val : ℕ) : ZMod M) := by
  rw [dirG_val, ← (Chr.clsFacts ℚ Ω N).2.1 M h, MonoidHom.comp_apply, ZMod.unitsMap_val, ZMod.natCast_val]

/- English proof (translation)
Introduce and unpack `rfl`. Use `h (MonoidHom.ext fun s => ?_)` and prove the remaining obligations. Rewrite using `[Chr.dirG, MonoidHom.comp_apply, Subsingleton.elim (Chr.cls ℚ Ω 1 s) 1, map_one, MonoidHom.one_apply]`.
-/
private theorem dirG_ne_one {M : ℕ} [NeZero M] {O : Type} [CommRing O] {χ : DirichletCharacter O M} (h : Chr.dirG ℚ Ω χ ≠ 1) : M ≠ 1 := by
  rintro rfl
  refine h (MonoidHom.ext fun s => ?_)
  rw [Chr.dirG, MonoidHom.comp_apply, Subsingleton.elim (Chr.cls ℚ Ω 1 s) 1, map_one, MonoidHom.one_apply]

end Gal

/- English proof (translation)
Use `⟨DirichletCharacter.changeLevel (dvd_mul_right M w) φ * DirichletCharacter.changeLevel (dvd_mul_left w M) θ, fun n => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : n.Coprime (M * w)`. Establish `h' : IsCoprime (n : ℤ) ((M * w : ℕ) : ℤ)` using `Nat.isCoprime_iff_coprime.2 h`. Establish `h1` using `DirichletCharacter.changeLevel_eq_cast_of_dvd' φ (dvd_mul_right M w) h'`. Establish `h2` using `DirichletCharacter.changeLevel_eq_cast_of_dvd' θ (dvd_mul_left w M) h'`.

Rewrite `h1`, `h2` using `[Int.cast_natCast, Int.cast_natCast]`. Rewrite using `[MulChar.mul_apply, h1, h2]`. Rewrite using `[MulChar.map_nonunit _ (fun h' => h ((ZMod.isUnit_iff_coprime _ _).1 h'))]`. Rewrite `h` using `[Nat.coprime_mul_iff_right, not_and_or]`. Break down `h with h | h` into its components or cases.

Rewrite using `[φ.map_nonunit (fun h' => h ((ZMod.isUnit_iff_coprime _ _).1 h')), zero_mul]`. Rewrite using `[θ.map_nonunit (fun h' => h ((ZMod.isUnit_iff_coprime _ _).1 h')), mul_zero]`.
-/
private theorem exists_mul {M w : ℕ} [NeZero (M * w)] (φ : DirichletCharacter ℂ M) (θ : DirichletCharacter ℂ w) :
    ∃ χ : DirichletCharacter ℂ (M * w), ∀ n : ℕ, χ (n : ZMod (M * w)) = φ (n : ZMod M) * θ (n : ZMod w) := by
  refine ⟨DirichletCharacter.changeLevel (dvd_mul_right M w) φ * DirichletCharacter.changeLevel (dvd_mul_left w M) θ, fun n => ?_⟩
  by_cases h : n.Coprime (M * w)
  · have h' : IsCoprime (n : ℤ) ((M * w : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 h
    have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' φ (dvd_mul_right M w) h'
    have h2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' θ (dvd_mul_left w M) h'
    rw [Int.cast_natCast, Int.cast_natCast] at h1 h2
    rw [MulChar.mul_apply, h1, h2]
  · rw [MulChar.map_nonunit _ (fun h' => h ((ZMod.isUnit_iff_coprime _ _).1 h'))]
    rw [Nat.coprime_mul_iff_right, not_and_or] at h
    rcases h with h | h
    · rw [φ.map_nonunit (fun h' => h ((ZMod.isUnit_iff_coprime _ _).1 h')), zero_mul]
    · rw [θ.map_nonunit (fun h' => h ((ZMod.isUnit_iff_coprime _ _).1 h')), mul_zero]

end UpperTheory.V.Sd.PadicNormCongruences
