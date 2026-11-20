import Mathlib
import GroundTheory.PAdicHodge.BCrisEigenWitt
import GroundTheory.PAdicHodge.LocalBridge
import GroundTheory.PAdicHodge.UnramifiedACris
import GroundTheory.PAdicHodge.UnramifiedClosure
import GroundTheory.LocalFields.WeilGroupDefs
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace EigenWitt

open Polynomial GroundTheory.LocalField

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p

/- English proof (translation)
Use `set P : (PadicAlgCl p)[X] := X ^ m - C 1 with hP`. Establish `hinj : Function.Injective (algebraMap (PadicAlgCl p) ℂ_[p])` using `(algebraMap (PadicAlgCl p) ℂ_[p]).injective`. Establish `hroots` using `(IsAlgClosed.splits P).roots_map_of_injective hinj`. Establish `hmem : z ∈ (P.map (algebraMap (PadicAlgCl p) ℂ_[p])).roots`. Rewrite using `[show P.map (algebraMap (PadicAlgCl p) ℂ_[p]) = X ^ m - C 1 by simp [hP], mem_roots (X_pow_sub_C_ne_zero hm 1)]`.

Simplify using `[hz]`. Rewrite `hmem` using `[hroots, Multiset.mem_map]`. Take `⟨ζ, hζ, hζz⟩` from `hmem`. Use `⟨ζ, hζz, ?_⟩` and prove the remaining obligations. Rewrite `hζ` using `[mem_roots (X_pow_sub_C_ne_zero hm 1)]`.

Simplify `hζ` using `[sub_eq_zero]`.
-/
theorem exists_padicAlgCl_eq_of_pow_eq_one {z : ℂ_[p]} {m : ℕ} (hm : 0 < m) (hz : z ^ m = 1) :
    ∃ ζ : PadicAlgCl p, algebraMap (PadicAlgCl p) ℂ_[p] ζ = z ∧ ζ ^ m = 1 := by
  classical
  set P : (PadicAlgCl p)[X] := X ^ m - C 1 with hP
  have hinj : Function.Injective (algebraMap (PadicAlgCl p) ℂ_[p]) :=
    (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  have hroots := (IsAlgClosed.splits P).roots_map_of_injective hinj
  have hmem : z ∈ (P.map (algebraMap (PadicAlgCl p) ℂ_[p])).roots := by
    rw [show P.map (algebraMap (PadicAlgCl p) ℂ_[p]) = X ^ m - C 1 by simp [hP],
      mem_roots (X_pow_sub_C_ne_zero hm 1)]
    simp [hz]
  rw [hroots, Multiset.mem_map] at hmem
  obtain ⟨ζ, hζ, hζz⟩ := hmem
  refine ⟨ζ, hζz, ?_⟩
  rw [mem_roots (X_pow_sub_C_ne_zero hm 1)] at hζ
  simpa [sub_eq_zero] using hζ

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

abbrev untiltC (x : 𝒪♭) : ℂ_[p] := ((PreTilt.untilt x : normInteger ℂ_[p]) : ℂ_[p])

/- English proof (translation)
Simplify using `[untiltC, map_pow]`.
-/
theorem untiltC_pow (x : 𝒪♭) (k : ℕ) : untiltC (x ^ k) = untiltC x ^ k := by
  simp [untiltC, map_pow]

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`.
-/
theorem norm_natCast_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, norm_algebraMap']
  exact Padic.norm_p_lt_one

/- English proof (translation)
Use `set z := x - y with hz`. Establish `hzp : z ^ p ^ n = z` using `by rw [hz, sub_pow_char_pow, hx, hy]`. Establish `hsum` using `norm_untilt_add_sub_le (K := ℂ_[p]) (p := p) z y`. Establish `hzy : z + y = x` using `by rw [hz, sub_add_cancel]`. Rewrite `hsum` using `[hzy]`.

Establish `e : ((PreTilt.untilt x : normInteger ℂ_[p]) : ℂ_[p]) - (((PreTilt.untilt z : normInteger ℂ_[p]) : ℂ_[p]) + ((PreTilt.untilt y : normInteger ℂ_[p]) : ℂ_[p])) = -untiltC z`. Simplify using `only [untiltC] at h ⊢`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hsum` using `[e, norm_neg]`.

Establish `hpow : ‖untiltC z‖ ^ p ^ n = ‖untiltC z‖` using `by rw [← norm_pow, ← untiltC_pow, hzp]`. Establish `hz0 : untiltC z = 0`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖untiltC z‖` using `norm_pos_iff.2 hne`. Establish `hpn : 1 < p ^ n` using `Nat.one_lt_pow hn.ne' hp.out.one_lt`.

Establish `h1 : ‖untiltC z‖ = 1`. Break down `lt_trichotomy ‖untiltC z‖ 1 with hlt | heq | hgt` into its components or cases. Establish `: ‖untiltC z‖ ^ p ^ n < ‖untiltC z‖ ^ 1` using `pow_lt_pow_right_of_lt_one₀ hpos hlt hpn`. Rewrite `this` using `[pow_one, hpow]`. Conclude with `absurd this (lt_irrefl _)`.

Conclude with `heq`. Establish `: ‖untiltC z‖ ^ 1 < ‖untiltC z‖ ^ p ^ n` using `pow_lt_pow_right₀ hgt hpn`. Rewrite `this` using `[pow_one, hpow]`. Conclude with `absurd this (lt_irrefl _)`. Rewrite `hsum` using `[h1]`.

Conclude with `absurd (lt_of_le_of_lt hsum norm_natCast_p_lt_one) (lt_irrefl _)`. Establish `hz' : z = 0` using `(untilt_eq_zero_iff (K := ℂ_[p])).1 hz0`. Conclude with `sub_eq_zero.1 hz'`.
-/
theorem eq_of_untiltC_eq {x y : 𝒪♭} {n : ℕ} (hn : 0 < n) (hx : x ^ p ^ n = x) (hy : y ^ p ^ n = y)
    (h : untiltC x = untiltC y) : x = y := by
  set z := x - y with hz
  have hzp : z ^ p ^ n = z := by rw [hz, sub_pow_char_pow, hx, hy]
  have hsum := norm_untilt_add_sub_le (K := ℂ_[p]) (p := p) z y
  have hzy : z + y = x := by rw [hz, sub_add_cancel]
  rw [hzy] at hsum
  have e : ((PreTilt.untilt x : normInteger ℂ_[p]) : ℂ_[p]) -
      (((PreTilt.untilt z : normInteger ℂ_[p]) : ℂ_[p]) +
        ((PreTilt.untilt y : normInteger ℂ_[p]) : ℂ_[p])) = -untiltC z := by
    simp only [untiltC] at h ⊢
    rw [h]
    ring
  rw [e, norm_neg] at hsum
  have hpow : ‖untiltC z‖ ^ p ^ n = ‖untiltC z‖ := by rw [← norm_pow, ← untiltC_pow, hzp]
  have hz0 : untiltC z = 0 := by
    by_contra hne
    have hpos : 0 < ‖untiltC z‖ := norm_pos_iff.2 hne
    have hpn : 1 < p ^ n := Nat.one_lt_pow hn.ne' hp.out.one_lt
    have h1 : ‖untiltC z‖ = 1 := by
      rcases lt_trichotomy ‖untiltC z‖ 1 with hlt | heq | hgt
      · have : ‖untiltC z‖ ^ p ^ n < ‖untiltC z‖ ^ 1 := pow_lt_pow_right_of_lt_one₀ hpos hlt hpn
        rw [pow_one, hpow] at this
        exact absurd this (lt_irrefl _)
      · exact heq
      · have : ‖untiltC z‖ ^ 1 < ‖untiltC z‖ ^ p ^ n := pow_lt_pow_right₀ hgt hpn
        rw [pow_one, hpow] at this
        exact absurd this (lt_irrefl _)
    rw [h1] at hsum
    exact absurd (lt_of_le_of_lt hsum norm_natCast_p_lt_one) (lt_irrefl _)
  have hz' : z = 0 := (untilt_eq_zero_iff (K := ℂ_[p])).1 hz0
  exact sub_eq_zero.1 hz'

/- English proof (translation)
Establish `hy : (galFlat σ x) ^ p ^ n = galFlat σ x` using `by rw [← map_pow, hx]`. Establish `hxa : (x ^ a) ^ p ^ n = x ^ a` using `by rw [← pow_mul, mul_comm, pow_mul, hx]`. Use `eq_of_untiltC_eq hn hy hxa ?_` and prove the remaining obligations. Establish `hpn : 1 ≤ p ^ n` using `Nat.one_le_pow _ _ hp.out.pos`. Distinguish the cases in `h0 : untiltC x = 0`.

Establish `hx0 : x = 0` using `(untilt_eq_zero_iff (K := ℂ_[p])).1 h0`. Rewrite using `[hx0, map_zero, zero_pow ha.ne']`. Establish `hux : untiltC x ^ p ^ n = untiltC x` using `by rw [← untiltC_pow, hx]`. Establish `hux1 : untiltC x ^ (p ^ n - 1) = 1`. Establish `e : untiltC x ^ (p ^ n - 1) * untiltC x = 1 * untiltC x`.

Rewrite using `[← pow_succ, Nat.sub_add_cancel hpn, hux, one_mul]`. Conclude with `mul_right_cancel₀ h0 e`. Establish `hm : 0 < p ^ n - 1`. Use `Nat.one_lt_pow hn.ne' hp.out.one_lt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Take `⟨ζ, hζ, hζ1⟩` from `exists_padicAlgCl_eq_of_pow_eq_one hm hux1`. Establish `e1 : untiltC (galFlat σ x) = σ • untiltC x` using `AInf.coe_untilt_gal σ x`. Rewrite using `[e1, untiltC_pow, ← hζ, ← PadicComplex.coe_eq, gal_smul_coe, hσ ζ hζ1, PadicComplex.coe_eq, map_pow]`. Both sides reduce to the same expression.
-/
theorem galFlat_eq_pow {σ : Gal(PadicAlgCl p/K)} {n a : ℕ} (hn : 0 < n) (ha : 0 < a)
    (hσ : ∀ ζ : PadicAlgCl p, ζ ^ (p ^ n - 1) = 1 → σ ζ = ζ ^ a) {x : 𝒪♭} (hx : x ^ p ^ n = x) :
    galFlat σ x = x ^ a := by
  have hy : (galFlat σ x) ^ p ^ n = galFlat σ x := by rw [← map_pow, hx]
  have hxa : (x ^ a) ^ p ^ n = x ^ a := by rw [← pow_mul, mul_comm, pow_mul, hx]
  refine eq_of_untiltC_eq hn hy hxa ?_
  have hpn : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.out.pos
  by_cases h0 : untiltC x = 0
  · have hx0 : x = 0 := (untilt_eq_zero_iff (K := ℂ_[p])).1 h0
    rw [hx0, map_zero, zero_pow ha.ne']
  · have hux : untiltC x ^ p ^ n = untiltC x := by rw [← untiltC_pow, hx]
    have hux1 : untiltC x ^ (p ^ n - 1) = 1 := by
      have e : untiltC x ^ (p ^ n - 1) * untiltC x = 1 * untiltC x := by
        rw [← pow_succ, Nat.sub_add_cancel hpn, hux, one_mul]
      exact mul_right_cancel₀ h0 e
    have hm : 0 < p ^ n - 1 := by
      have := Nat.one_lt_pow hn.ne' hp.out.one_lt
      omega
    obtain ⟨ζ, hζ, hζ1⟩ := exists_padicAlgCl_eq_of_pow_eq_one hm hux1
    have e1 : untiltC (galFlat σ x) = σ • untiltC x := AInf.coe_untilt_gal σ x
    rw [e1, untiltC_pow, ← hζ, ← PadicComplex.coe_eq, gal_smul_coe, hσ ζ hζ1, PadicComplex.coe_eq,
      map_pow]
    rfl

open ValuativeRel

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]

omit [FiniteDimensional ℚ_[p] L] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨inferInstance, inferInstance⟩`.
-/
theorem isSepClosure_padicAlgCl : IsSepClosure L (PadicAlgCl p) :=
  ⟨inferInstance, inferInstance⟩

/- English proof (translation)
Establish `hpn : 1 ≤ p ^ n` using `Nat.one_le_pow _ _ hp.out.pos`. Rewrite using `[Nat.cast_sub hpn, Nat.cast_pow, CharP.cast_eq_zero, zero_pow hn.ne', Nat.cast_one, zero_sub]`. Conclude with `neg_ne_zero.2 one_ne_zero`.
-/
theorem natCast_pow_sub_one_ne_zero {n : ℕ} (hn : 0 < n) :
    ((p ^ n - 1 : ℕ) : 𝓀[L]) ≠ 0 := by
  have hpn : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.out.pos
  rw [Nat.cast_sub hpn, Nat.cast_pow, CharP.cast_eq_zero, zero_pow hn.ne', Nat.cast_one, zero_sub]
  exact neg_ne_zero.2 one_ne_zero

/- English proof (translation)
The claim follows from `mem_unramifiedRoots_iff.2 ⟨p ^ n - 1, natCast_pow_sub_one_ne_zero hn, hζ⟩`.
-/
theorem mem_unramifiedRoots_of_pow_eq_one {ζ : PadicAlgCl p} {n : ℕ} (hn : 0 < n)
    (hζ : ζ ^ (p ^ n - 1) = 1) : ζ ∈ unramifiedRoots L (PadicAlgCl p) :=
  mem_unramifiedRoots_iff.2 ⟨p ^ n - 1, natCast_pow_sub_one_ne_zero hn, hζ⟩

/- English proof (translation)
Apply `fpbarToPreTilt_injective` to reduce the goal to its premises. Take `⟨n, hn, hx⟩` from `fpbarToPreTilt_pow_eq_self a`. Rewrite using `[fpbarToPreTilt_galFpbar, map_pow]`. Conclude with `galFlat_eq_pow hn Nat.card_pos (fun ζ hζ => (unramifiedDegree_eq_ofAdd_one_iff σ).1 hσ ζ (mem_unramifiedRoots_of_pow_eq_one hn hζ)) hx`.
-/
theorem galFpbar_eq_pow_of_degree_one {σ : Gal(PadicAlgCl p/L)}
    (hσ : unramifiedDegree L (PadicAlgCl p) σ = Multiplicative.ofAdd 1) (a : Fpbar p) :
    galFpbar σ a = a ^ Nat.card 𝓀[L] := by
  apply fpbarToPreTilt_injective
  obtain ⟨n, hn, hx⟩ := fpbarToPreTilt_pow_eq_self a
  rw [fpbarToPreTilt_galFpbar, map_pow]
  exact galFlat_eq_pow hn Nat.card_pos (fun ζ hζ =>
    (unramifiedDegree_eq_ofAdd_one_iff σ).1 hσ ζ (mem_unramifiedRoots_of_pow_eq_one hn hζ)) hx

/- English proof (translation)
Establish `hker : σ ∈ (maximalUnramifiedExtension L (PadicAlgCl p)).fixingSubgroup`. Rewrite using `[← ker_unramifiedDegree]`. Conclude with `hσ`. Apply `fpbarToPreTilt_injective` to reduce the goal to its premises. Take `⟨n, hn, hx⟩` from `fpbarToPreTilt_pow_eq_self a`.

Rewrite using `[fpbarToPreTilt_galFpbar]`. Use `galFlat_eq_pow (σ := σ) hn one_pos (fun ζ hζ => by` as an intermediate fact. Rewrite using `[pow_one]`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hker ζ (unramifiedRoots_subset_maximalUnramifiedExtension (mem_unramifiedRoots_of_pow_eq_one hn hζ))) hx`. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis.
-/
theorem galFpbar_eq_self {σ : Gal(PadicAlgCl p/L)} (hσ : unramifiedDegree L (PadicAlgCl p) σ = 1)
    (a : Fpbar p) : galFpbar σ a = a := by
  have hker : σ ∈ (maximalUnramifiedExtension L (PadicAlgCl p)).fixingSubgroup := by
    rw [← ker_unramifiedDegree]
    exact hσ
  apply fpbarToPreTilt_injective
  obtain ⟨n, hn, hx⟩ := fpbarToPreTilt_pow_eq_self a
  rw [fpbarToPreTilt_galFpbar]
  have := galFlat_eq_pow (σ := σ) hn one_pos (fun ζ hζ => by
    rw [pow_one]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hker ζ
      (unramifiedRoots_subset_maximalUnramifiedExtension (mem_unramifiedRoots_of_pow_eq_one hn hζ))) hx
  rwa [pow_one] at this

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[WittVector.map_coeff, iterateFrobenius_def]`. Proceed by induction on `f with`. Consider the case `zero => simp`. Consider the case `succ f ih`.

Rewrite using `[Function.iterate_succ_apply', WittVector.coeff_frobenius_charP, ← ih, ← pow_mul, ← pow_succ]`.
-/
theorem map_iterateFrobenius (f : ℕ) (x : WittVector p (Fpbar p)) :
    WittVector.map (iterateFrobenius (Fpbar p) p f) x = WittVector.frobenius^[f] x := by
  ext n
  rw [WittVector.map_coeff, iterateFrobenius_def]
  induction f with
  | zero => simp
  | succ f ih =>
    rw [Function.iterate_succ_apply', WittVector.coeff_frobenius_charP, ← ih, ← pow_mul, ← pow_succ]

/- English proof (translation)
Proceed by induction on `f with`. Consider the case `zero => simp`. Consider the case `succ f ih`. Rewrite using `[Function.iterate_succ_apply', ih, map_mul, hb, frobenius_padicIntToWittFpbar, map_pow, map_pow, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iterate_frobenius_eq_mul {w : ℤ_[p]ˣ} {b : WittVector p (Fpbar p)}
    (hb : WittVector.frobenius b = b * padicIntToWittFpbar (w : ℤ_[p])) (f : ℕ) :
    WittVector.frobenius^[f] b = b * padicIntToWittFpbar ((w : ℤ_[p]) ^ f) := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, hb, frobenius_padicIntToWittFpbar, map_pow,
      map_pow, pow_succ]
    ring

/- English proof (translation)
Establish `e : galFpbar σ = iterateFrobenius (Fpbar p) p f`. Use extensionality with `a`. Rewrite using `[galFpbar_eq_pow_of_degree_one hσ, hq, iterateFrobenius_def]`. Rewrite using `[gal_smul_wittToAInf, e, map_iterateFrobenius, iterate_frobenius_eq_mul hb, map_mul, wittToAInf_padicIntToWittFpbar, mul_comm]`.
-/
theorem gal_smul_twist_of_degree_one {w : ℤ_[p]ˣ} {b : WittVector p (Fpbar p)}
    (hb : WittVector.frobenius b = b * padicIntToWittFpbar (w : ℤ_[p])) {f : ℕ}
    (hq : Nat.card 𝓀[L] = p ^ f) {σ : Gal(PadicAlgCl p/L)}
    (hσ : unramifiedDegree L (PadicAlgCl p) σ = Multiplicative.ofAdd 1) :
    σ • wittToAInf b = IsPerfectoidField.padicIntToWitt p ((w : ℤ_[p]) ^ f) * wittToAInf b := by
  have e : galFpbar σ = iterateFrobenius (Fpbar p) p f := by
    ext a
    rw [galFpbar_eq_pow_of_degree_one hσ, hq, iterateFrobenius_def]
  rw [gal_smul_wittToAInf, e, map_iterateFrobenius, iterate_frobenius_eq_mul hb, map_mul,
    wittToAInf_padicIntToWittFpbar, mul_comm]

/- English proof (translation)
Establish `e : galFpbar σ = RingHom.id (Fpbar p)` using `RingHom.ext (galFpbar_eq_self hσ)`. Rewrite using `[gal_smul_wittToAInf, e, WittVector.map_id]`. Both sides reduce to the same expression.
-/
theorem gal_smul_twist_of_inertia (b : WittVector p (Fpbar p)) {σ : Gal(PadicAlgCl p/L)}
    (hσ : unramifiedDegree L (PadicAlgCl p) σ = 1) : σ • wittToAInf b = wittToAInf b := by
  have e : galFpbar σ = RingHom.id (Fpbar p) := RingHom.ext (galFpbar_eq_self hσ)
  rw [gal_smul_wittToAInf, e, WittVector.map_id]
  rfl

/- English proof (translation)
Set `` to `Fintype.ofFinite 𝓀[L]`. Take `⟨n, -, hcard⟩` from `FiniteField.card 𝓀[L] p`. Conclude with `⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hcard]⟩`.
-/
theorem exists_card_residueField_eq_pow : ∃ f : ℕ, 0 < f ∧ Nat.card 𝓀[L] = p ^ f := by
  let := Fintype.ofFinite 𝓀[L]
  obtain ⟨n, -, hcard⟩ := FiniteField.card 𝓀[L] p
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hcard]⟩

/- English proof (translation)
Use `isSepClosure_padicAlgCl (L := L)` as an intermediate fact. Set `H : Subgroup Gal(PadicAlgCl p/L)` to `{ carrier := {τ | ρ τ = 1} mul_mem' := fun {a b} (ha : ρ a = 1) (hb : ρ b = 1) => show ρ (a * b) = 1 by`. Rewrite using `[map_mul, ha, hb, one_mul]`. Use the proof step `one_mem' := map_one ρ`. Use the proof step `inv_mem' := fun {a} (ha : ρ a = 1) => show ρ a⁻¹ = 1 by`.

Combine the equalities or inequalities in the displayed calculation. Establish `hclosed : IsClosed (H : Set Gal(PadicAlgCl p/L))` using `isClosed_eq hρ continuous_const`. Establish `hW : (weilSubgroup L (PadicAlgCl p) : Set Gal(PadicAlgCl p/L)) ⊆ H`. Introduce `τ hτ`. Take `⟨n, hn⟩` from `mem_weilSubgroup_iff_unramifiedDegree.1 hτ`.

Establish `hdeg : unramifiedDegree L (PadicAlgCl p) (σ₀ ^ n) = unramifiedDegree L (PadicAlgCl p) τ`. Rewrite using `[map_zpow, hσ₀, hn, ← ofAdd_zsmul, zsmul_one]`. Establish `h1 : unramifiedDegree L (PadicAlgCl p) ((σ₀ ^ n)⁻¹ * τ) = 1`. Rewrite using `[map_mul, map_inv, hdeg, inv_mul_cancel]`. Establish `hσ₀H : σ₀ ∈ H` using `h₀`.

Establish `hpow : σ₀ ^ n ∈ H` using `H.zpow_mem hσ₀H n`. Establish `hrest : (σ₀ ^ n)⁻¹ * τ ∈ H` using `hI _ h1`. Use `H.mul_mem hpow hrest` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis. Establish `hsub : closure (weilSubgroup L (PadicAlgCl p) : Set Gal(PadicAlgCl p/L)) ⊆ H` using `closure_minimal hW hclosed`.

Rewrite `hsub` using `[(dense_weilSubgroup L (PadicAlgCl p)).closure_eq]`. Conclude with `hsub (Set.mem_univ σ)`.
-/
theorem eq_one_of_degree_one (ρ : Gal(PadicAlgCl p/L) →* ℂ_[p]) (hρ : Continuous ρ)
    {σ₀ : Gal(PadicAlgCl p/L)}
    (hσ₀ : unramifiedDegree L (PadicAlgCl p) σ₀ = Multiplicative.ofAdd 1) (h₀ : ρ σ₀ = 1)
    (hI : ∀ σ, unramifiedDegree L (PadicAlgCl p) σ = 1 → ρ σ = 1) (σ : Gal(PadicAlgCl p/L)) :
    ρ σ = 1 := by
  have := isSepClosure_padicAlgCl (L := L)
  let H : Subgroup Gal(PadicAlgCl p/L) :=
    { carrier := {τ | ρ τ = 1}
      mul_mem' := fun {a b} (ha : ρ a = 1) (hb : ρ b = 1) => show ρ (a * b) = 1 by
        rw [map_mul, ha, hb, one_mul]
      one_mem' := map_one ρ
      inv_mem' := fun {a} (ha : ρ a = 1) => show ρ a⁻¹ = 1 by
        calc ρ a⁻¹ = ρ a⁻¹ * ρ a := by rw [ha, mul_one]
          _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one] }
  have hclosed : IsClosed (H : Set Gal(PadicAlgCl p/L)) := isClosed_eq hρ continuous_const
  have hW : (weilSubgroup L (PadicAlgCl p) : Set Gal(PadicAlgCl p/L)) ⊆ H := by
    intro τ hτ
    obtain ⟨n, hn⟩ := mem_weilSubgroup_iff_unramifiedDegree.1 hτ
    have hdeg : unramifiedDegree L (PadicAlgCl p) (σ₀ ^ n) = unramifiedDegree L (PadicAlgCl p) τ := by
      rw [map_zpow, hσ₀, hn, ← ofAdd_zsmul, zsmul_one]
    have h1 : unramifiedDegree L (PadicAlgCl p) ((σ₀ ^ n)⁻¹ * τ) = 1 := by
      rw [map_mul, map_inv, hdeg, inv_mul_cancel]
    have hσ₀H : σ₀ ∈ H := h₀
    have hpow : σ₀ ^ n ∈ H := H.zpow_mem hσ₀H n
    have hrest : (σ₀ ^ n)⁻¹ * τ ∈ H := hI _ h1
    have := H.mul_mem hpow hrest
    rwa [mul_inv_cancel_left] at this
  have hsub : closure (weilSubgroup L (PadicAlgCl p) : Set Gal(PadicAlgCl p/L)) ⊆ H :=
    closure_minimal hW hclosed
  rw [(dense_weilSubgroup L (PadicAlgCl p)).closure_eq] at hsub
  exact hsub (Set.mem_univ σ)

end EigenWitt

end GroundTheory.PAdicHodge
