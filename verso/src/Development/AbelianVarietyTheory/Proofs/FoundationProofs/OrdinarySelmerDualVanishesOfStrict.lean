import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Foundations.CohomologyInputsOfUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergOrdinaryOfVanishingOnCycloKernel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTwoCocycleReciprocityTrivialAtLastPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductUnramifiedClassesVanishesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCocycleIntegralAfterScalingStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductDualTwistIsTwoCocycleUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalDualityCharacterOrthogonalClassesStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.Upgrade

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Simplify using `[mat]`.
-/
theorem mat_mul (W : R2 Ω l) (s t : G ℚ Ω) : mat W (s * t) = mat W s * mat W t := by simp [mat]

/- English proof (translation)
Simplify using `[mat]`.
-/
theorem mat_one (W : R2 Ω l) : mat W 1 = 1 := by simp [mat]

/- English proof (translation)
Rewrite using `[Matrix.det_fin_two, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_upper (W : R2 Ω l) {s : G ℚ Ω} (h : mat W s 1 0 = 0) : (mat W s).det = mat W s 0 0 * mat W s 1 1 := by
  rw [Matrix.det_fin_two, h]; ring

/- English proof (translation)
Rewrite using `[CupCob.mat_dual1 W h, Matrix.smul_apply, smul_eq_mul]`.
-/
theorem galoisRepRankTwoTateDual_matrix_apply (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) (i j : Fin 2) :
    mat (dual1 W) s i j = eps l s * (mat W s).det * mat W s i j := by
  rw [CupCob.mat_dual1 W h, Matrix.smul_apply, smul_eq_mul]

/- English proof (translation)
Establish `hm : Continuous fun s => mat W s` using `Units.continuous_val.comp hc`. Establish `hf : Continuous fun s => mat (dual1 W) s`. Repeatedly rewrite using `[CupCob.mat_dual1 W h]`. Conclude with `(CupCob.eps_cont.mul hm.matrix_det).smul hm`. Rewrite using `[Units.continuous_iff]`.

Prove the components needed by the constructor for the conclusion. Conclude with `hf`. Establish `e : ∀ s, (((dual1 W s)⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) = mat (dual1 W) s⁻¹`. Introduce `s`. Simplify using `only [mat, map_inv]`.

Repeatedly rewrite using `[e]`. Conclude with `hf.comp continuous_inv`.
-/
theorem continuous_galoisRepRankTwoTateDual (W : R2 Ω l) (h : dt W ^ 2 = 1) (hc : Continuous W) : Continuous (dual1 W) := by
  have hm : Continuous fun s => mat W s := Units.continuous_val.comp hc
  have hf : Continuous fun s => mat (dual1 W) s := by
    simp_rw [CupCob.mat_dual1 W h]
    exact (CupCob.eps_cont.mul hm.matrix_det).smul hm
  rw [Units.continuous_iff]
  constructor
  · exact hf
  · have e : ∀ s, (((dual1 W s)⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) = mat (dual1 W) s⁻¹ := by
      intro s; simp only [mat, map_inv]
    simp_rw [e]
    exact hf.comp continuous_inv

/- English proof (translation)
The claim follows from `CupCob.det_sq W h s`.
-/
theorem dt_sq_apply (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) : (mat W s).det ^ 2 = 1 := CupCob.det_sq W h s

/- English proof (translation)
Use `set D := Dec (F := ℚ) A with hDdef`. Establish `hup : ∀ s ∈ D, mat W s 1 0 = 0` using `hW.upper`. Establish `h00 : ∀ s t, t ∈ D → mat W (s * t) 0 0 = mat W s 0 0 * mat W t 0 0`. Introduce `s t ht`. Rewrite using `[mat_mul, Matrix.mul_apply, Fin.sum_univ_two, hup t ht]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hv : A.valuation (l : Ω) < 1`. Take `⟨v, hA, hlv⟩` from `hW.atL`. Simplify using `using (hA _).2 hlv`. Take `⟨u0, hu0⟩` from `GrOfKill.exists_unit_one_add l`.

Take `⟨t, htI, htu⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u0`. Establish `heps : eps l t = ((1 + l : ℕ) : Qbar l)`. Simplify using `[eps, cycBar, htu, hu0]`. Take `⟨m, hm1, hm⟩` from `hW.wt`. Establish `htD : t ∈ D` using `Ine_le_Dec A htI`.

Establish `hpow00 : ∀ s ∈ D, ∀ n : ℕ, mat W (s ^ n) 0 0 = mat W s 0 0 ^ n`. Introduce `s hs n`. Proceed by induction on `n with`. Consider the case `zero => simp [mat_one]`. Consider the case `succ n ih => rw [pow_succ, h00 _ _ hs, ih, pow_succ]`.

Use `set T := t ^ (2 * m) with hTdef`. Establish `hTD : T ∈ D` using `D.pow_mem htD _`. Use `set Nq : ℕ := (1 + l) ^ (2 * (e * m)) with hNq`. Establish `hT00 : mat W T 0 0 = (Nq : Qbar l)`. Rewrite using `[hTdef, hpow00 t htD, pow_mul', hm t htI, heps, hNq]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hdT : (mat W T).det = 1`. Establish `h2 : dt W t ^ 2 = 1`. Use `congrArg (fun f => f t) hW.det2` as an intermediate fact.

Simplify using `using this`. Establish `h3 : dt W T = 1` using `by rw [hTdef, map_pow, pow_mul, h2, one_pow]`. Establish `h4 : ((dt W T : (Qbar l)ˣ) : Qbar l) = (mat W T).det` using `rfl`. Rewrite using `[← h4, h3, Units.val_one]`. Establish `hepsT : eps l T = (((1 + l) ^ (2 * m) : ℕ) : Qbar l)`.

Establish `: eps l T = eps l t ^ (2 * m)` using `by simp [hTdef, eps]`. Rewrite using `[this, heps]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hl1 : 1 < 1 + l` using `by have := (Fact.out : l.Prime).two_le; omega`.

Establish `hNq1 : 1 < Nq`. Rewrite using `[hNq]; exact Nat.one_lt_pow (by have := hW.e_pos; positivity) hl1`. Use `⟨⟨T, hTD, fun h => ?_⟩, ⟨T, hTD, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `h5 : (Nq : Qbar l) * 1 = 1`. Establish `h7` using `det_upper W (hup T hTD)`.

Rewrite `h7` using `[hdT, hT00, h]`. Conclude with `h7.symm`. Establish `h6 : Nq = 1` using `by exact_mod_cast (mul_one (Nq : Qbar l)).symm.trans h5`. Use linear arithmetic over natural numbers and integers. Rewrite `h` using `[galoisRepRankTwoTateDual_matrix_apply W hW.det2, hdT, hepsT, hT00]`.

Establish `h6 : (1 + l) ^ (2 * m) * Nq = 1` using `by exact_mod_cast (by simpa using h : ((((1 + l) ^ (2 * m) * Nq : ℕ)) : Qbar l) = 1)`. Establish `: 1 < (1 + l) ^ (2 * m) * Nq` using `one_lt_mul_of_le_of_lt (Nat.one_le_pow _ _ (by omega)) hNq1`. Use linear arithmetic over natural numbers and integers.
-/
theorem nontriv (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) [IsAlgClosure ℚ Ω] (W : R2 Ω l) (hW : Nf e S A W) :
    (∃ s ∈ Dec (F := ℚ) A, mat W s 1 1 ≠ 1) ∧ (∃ s ∈ Dec (F := ℚ) A, mat (dual1 W) s 0 0 ≠ 1) := by
  set D := Dec (F := ℚ) A with hDdef
  have hup : ∀ s ∈ D, mat W s 1 0 = 0 := hW.upper
  have h00 : ∀ s t, t ∈ D → mat W (s * t) 0 0 = mat W s 0 0 * mat W t 0 0 := by
    intro s t ht; rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_two, hup t ht]; ring
  have hv : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hA, hlv⟩ := hW.atL
    simpa using (hA _).2 hlv
  obtain ⟨u0, hu0⟩ := GrOfKill.exists_unit_one_add l
  obtain ⟨t, htI, htu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u0
  have heps : eps l t = ((1 + l : ℕ) : Qbar l) := by
    simp [eps, cycBar, htu, hu0]
  obtain ⟨m, hm1, hm⟩ := hW.wt
  have htD : t ∈ D := Ine_le_Dec A htI
  have hpow00 : ∀ s ∈ D, ∀ n : ℕ, mat W (s ^ n) 0 0 = mat W s 0 0 ^ n := by
    intro s hs n
    induction n with
    | zero => simp [mat_one]
    | succ n ih => rw [pow_succ, h00 _ _ hs, ih, pow_succ]
  set T := t ^ (2 * m) with hTdef
  have hTD : T ∈ D := D.pow_mem htD _
  set Nq : ℕ := (1 + l) ^ (2 * (e * m)) with hNq
  have hT00 : mat W T 0 0 = (Nq : Qbar l) := by
    rw [hTdef, hpow00 t htD, pow_mul', hm t htI, heps, hNq]; push_cast; ring
  have hdT : (mat W T).det = 1 := by
    have h2 : dt W t ^ 2 = 1 := by
      have := congrArg (fun f => f t) hW.det2
      simpa using this
    have h3 : dt W T = 1 := by rw [hTdef, map_pow, pow_mul, h2, one_pow]
    have h4 : ((dt W T : (Qbar l)ˣ) : Qbar l) = (mat W T).det := rfl
    rw [← h4, h3, Units.val_one]
  have hepsT : eps l T = (((1 + l) ^ (2 * m) : ℕ) : Qbar l) := by
    have : eps l T = eps l t ^ (2 * m) := by simp [hTdef, eps]
    rw [this, heps]; push_cast; ring
  have hl1 : 1 < 1 + l := by have := (Fact.out : l.Prime).two_le; omega
  have hNq1 : 1 < Nq := by
    rw [hNq]; exact Nat.one_lt_pow (by have := hW.e_pos; positivity) hl1
  refine ⟨⟨T, hTD, fun h => ?_⟩, ⟨T, hTD, fun h => ?_⟩⟩
  · have h5 : (Nq : Qbar l) * 1 = 1 := by
      have h7 := det_upper W (hup T hTD)
      rw [hdT, hT00, h] at h7
      exact h7.symm
    have h6 : Nq = 1 := by exact_mod_cast (mul_one (Nq : Qbar l)).symm.trans h5
    omega
  · rw [galoisRepRankTwoTateDual_matrix_apply W hW.det2, hdT, hepsT, hT00] at h
    have h6 : (1 + l) ^ (2 * m) * Nq = 1 := by exact_mod_cast (by simpa using h : ((((1 + l) ^ (2 * m) * Nq : ℕ)) : Qbar l) = 1)
    have : 1 < (1 + l) ^ (2 * m) * Nq := one_lt_mul_of_le_of_lt (Nat.one_le_pow _ _ (by omega)) hNq1
    omega

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hne' : v.asIdeal ≠ w.asIdeal` using `fun h => hne (HeightOneSpectrum.ext h)`. Establish `hmax : v.asIdeal ⊔ w.asIdeal = ⊤` using `Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal hne'`. Establish `hmul : v.asIdeal * w.asIdeal = v.asIdeal ⊓ w.asIdeal` using `Ideal.mul_eq_inf_of_coprime hmax`. Establish `hle : Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal * w.asIdeal`.

Rewrite using `[hmul, Ideal.span_singleton_le_iff_mem]`. Conclude with `⟨hv, hw⟩`. Establish `hd` using `Ideal.absNorm_dvd_absNorm_of_le hle`. Rewrite `hd` using `[Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one, map_mul]`. Establish `h1` using `NumberField.HeightOneSpectrum.one_lt_absNorm v`.

Establish `h2` using `NumberField.HeightOneSpectrum.one_lt_absNorm w`. Establish `hp : l.Prime` using `Fact.out`. Establish `ha : Ideal.absNorm v.asIdeal = l` using `(hp.eq_one_or_self_of_dvd _ (dvd_of_mul_right_dvd hd)).resolve_left (by omega)`. Establish `hb : Ideal.absNorm w.asIdeal = l` using `(hp.eq_one_or_self_of_dvd _ (dvd_of_mul_left_dvd hd)).resolve_left (by omega)`. Rewrite `hd` using `[ha, hb]`.

Use `Nat.le_of_dvd hp.pos hd` as an intermediate fact. Use `hp.two_le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem place_unique {v w : Pl} (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  by_contra hne
  have hne' : v.asIdeal ≠ w.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have hmax : v.asIdeal ⊔ w.asIdeal = ⊤ := Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal hne'
  have hmul : v.asIdeal * w.asIdeal = v.asIdeal ⊓ w.asIdeal := Ideal.mul_eq_inf_of_coprime hmax
  have hle : Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal * w.asIdeal := by
    rw [hmul, Ideal.span_singleton_le_iff_mem]; exact ⟨hv, hw⟩
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one, map_mul] at hd
  have h1 := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have h2 := NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hp : l.Prime := Fact.out
  have ha : Ideal.absNorm v.asIdeal = l :=
    (hp.eq_one_or_self_of_dvd _ (dvd_of_mul_right_dvd hd)).resolve_left (by omega)
  have hb : Ideal.absNorm w.asIdeal = l :=
    (hp.eq_one_or_self_of_dvd _ (dvd_of_mul_left_dvd hd)).resolve_left (by omega)
  rw [ha, hb] at hd
  have := Nat.le_of_dvd hp.pos hd
  have := hp.two_le
  nlinarith

/- English proof (translation)
Rewrite using `[ha.2 s t]`. Both sides reduce to the same expression.
-/
theorem coc_eq (V : R2 Ω l) {a : G ℚ Ω → Fin 2 → Qbar l} (ha : a ∈ Z1 (Loc.colRep V)) (s t : G ℚ Ω) :
    a (s * t) = a s + mat V s *ᵥ a t := by
  rw [ha.2 s t]; rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨ha.1.continuousOn, hint, fun s _ t _ i => by rw [coc_eq V ha s t]; simp [Cg]⟩`.
-/
theorem isIntegralCocycleOneModPow_of_integral_cocycle (c : Coef l) (n : ℕ) (V : R2 Ω l) (H : Subgroup (G ℚ Ω)) {a : G ℚ Ω → Fin 2 → Qbar l}
    (ha : a ∈ Z1 (Loc.colRep V)) (hint : ∀ s i, a s i ∈ c.O) : Coc1 c n V H a :=
  ⟨ha.1.continuousOn, hint, fun s _ t _ i => by rw [coc_eq V ha s t]; simp [Cg]⟩

/- English proof (translation)
Take `⟨x, hx, h⟩` from `h`. Conclude with `⟨x, hx, fun s hs i => by rw [h s hs]; simp [Cg]⟩`.
-/
theorem isIntegralCoboundaryOneModPow_of_integral_vector (c : Coef l) (n : ℕ) (V : R2 Ω l) (H : Subgroup (G ℚ Ω)) {a : G ℚ Ω → Fin 2 → Qbar l}
    (h : ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c.O) ∧ ∀ s ∈ H, a s = mat V s *ᵥ x - x) : Cob1 c n V H a := by
  obtain ⟨x, hx, h⟩ := h
  exact ⟨x, hx, fun s hs i => by rw [h s hs]; simp [Cg]⟩

/- English proof (translation)
Take `⟨u, hu, hui, hc⟩` from `h`. Conclude with `⟨u, hu, hui, fun s hs t ht => by rw [← e s hs t ht]; exact hc s hs t ht⟩`.
-/
theorem kummerTower_coboundaryTwo_congr {c : Coef l} {n : ℕ} {H : Subgroup (G ℚ Ω)} {ξ ξ' : G ℚ Ω → G ℚ Ω → Qbar l} (h : Cob2 c n H ξ)
    (e : ∀ s ∈ H, ∀ t ∈ H, ξ s t = ξ' s t) : Cob2 c n H ξ' := by
  obtain ⟨u, hu, hui, hc⟩ := h
  exact ⟨u, hu, hui, fun s hs t ht => by rw [← e s hs t ht]; exact hc s hs t ht⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem amitsur_d0_apply (V : R2 Ω l) (v : Fin 2 → Qbar l) (s : G ℚ Ω) :
    d0 (Loc.colRep V) v s = mat V s *ᵥ v - v := rfl

/- English proof (translation)
Use `⟨?_, fun g h => ?_⟩` and prove the remaining obligations. Establish `e : d0 (Loc.colRep V) v = fun s => mat V s *ᵥ v - v` using `funext fun s => amitsur_d0_apply V v s`. Rewrite using `[e]`. Conclude with `((Units.continuous_val.comp hc).matrix_mulVec continuous_const).sub continuous_const`. Express the relevant statement in the definitionally equal form `d0 (Loc.colRep V) v (g * h) = d0 (Loc.colRep V) v g + mat V g *ᵥ d0 (Loc.colRep V) v h`.

Rewrite using `[amitsur_d0_apply, amitsur_d0_apply, amitsur_d0_apply, mat_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem commAlgFunctorCoboundaryZero_mem_cocyclesOne (V : R2 Ω l) (hc : Continuous V) (v : Fin 2 → Qbar l) : d0 (Loc.colRep V) v ∈ Z1 (Loc.colRep V) := by
  refine ⟨?_, fun g h => ?_⟩
  · have e : d0 (Loc.colRep V) v = fun s => mat V s *ᵥ v - v := funext fun s => amitsur_d0_apply V v s
    rw [e]
    exact ((Units.continuous_val.comp hc).matrix_mulVec continuous_const).sub continuous_const
  · change d0 (Loc.colRep V) v (g * h) = d0 (Loc.colRep V) v g + mat V g *ᵥ d0 (Loc.colRep V) v h
    rw [amitsur_d0_apply, amitsur_d0_apply, amitsur_d0_apply, mat_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    abel

/- English proof (translation)
Introduce `w hw B hB s hs`. Establish `h1 : W s = 1` using `hu w hw B hB hs`. Establish `h2 : eps l s = 1`. Rewrite using `[Test.eps_eq, Test.cycZ_ine (fun h' => hw (hS w h')) hB hs]`. Simplify using the standard rewrite rules.

Rewrite using `[MonoidHom.mem_ker]`. Use `Units.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mat (dual1 W) s = 1`. Rewrite using `[CupCob.mat_dual1 W h, h2]`. Simplify using `[mat, h1]`.
-/
theorem galoisRepRankTwoTateDual_unramified_outside [IsAlgClosure ℚ Ω] (S : Finset Pl) (W : R2 Ω l) (h : dt W ^ 2 = 1) (hS : ContainsAbove S l)
    (hu : ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) :
    ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ (dual1 W).ker := by
  intro w hw B hB s hs
  have h1 : W s = 1 := hu w hw B hB hs
  have h2 : eps l s = 1 := by
    rw [Test.eps_eq, Test.cycZ_ine (fun h' => hw (hS w h')) hB hs]; simp
  rw [MonoidHom.mem_ker]
  refine Units.ext ?_
  change mat (dual1 W) s = 1
  rw [CupCob.mat_dual1 W h, h2]
  simp [mat, h1]

/- English proof (translation)
Introduce `hLit l _ Ω _ _ _ e S A W hW hES hStr z hz hzU hzGr`. Take `⟨c, y, S', hWc, hy, hyint, hyU, hyGr, -⟩` from `hES`. Establish `hdet2` using `hW.det2`. Establish `hc` using `hW.cont`. Establish `hc' : Continuous (dual1 W)` using `continuous_galoisRepRankTwoTateDual W hdet2 hc`.

Establish `hup : ∀ s ∈ Dec (F` using `ℚ) A, mat W s 1 0 = 0 := hW.upper`. Establish `hup' : ∀ s ∈ Dec (F` using `ℚ) A, mat (dual1 W) s 1 0 = 0 := fun s hs => by`. Rewrite using `[galoisRepRankTwoTateDual_matrix_apply W hdet2, hup s hs, mul_zero]`. Take `⟨c1, j, hc1, hyint1, hyunr1, -, -⟩` from `GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S W c y hc hWc hW.unr hy hyU A`. Establish `hWc1 : ∀ s i j, mat W s i j ∈ c1.O` using `fun s i j => hc1 (hWc s i j)`.

Establish `hW'c1 : ∀ s i j, mat (dual1 W) s i j ∈ c1.O` using `CupCob.dual_representation_integral c1 W hdet2 hWc1`. Take `⟨c2, k, hc2, hzint2, hzunr2, -, hzgr2⟩` from `GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S (dual1 W) c1 z hc' hW'c1 (galoisRepRankTwoTateDual_unramified_outside S W hdet2 hW.above hW.unr) hz hzU A`. Take `⟨x, hxO, hx⟩` from `hzgr2 hzGr`. Establish `hWc2 : ∀ s i j, mat W s i j ∈ c2.O` using `fun s i j => hc2 (hWc1 s i j)`. Establish `hW'c2 : ∀ s i j, mat (dual1 W) s i j ∈ c2.O` using `CupCob.dual_representation_integral c2 W hdet2 hWc2`.

Establish `hL : ((l : ℕ) : Qbar l) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`. Use `set L : Qbar l := ((l : ℕ) : Qbar l) with hLdef`. Use `set v0 : Fin 2 → Qbar l := ![0, x] with hv0`. Establish `hv0O : ∀ i, v0 i ∈ c2.O` using `fun i => by fin_cases i`. Simplify `c2.O.zero_mem` using `[hv0]`.

Simplify `hxO` using `[hv0]`. Use `set y1 : G ℚ Ω → Fin 2 → Qbar l := L ^ j • y with hy1`. Use `set z1 : G ℚ Ω → Fin 2 → Qbar l := L ^ k • z - d0 (Loc.colRep (dual1 W)) v0 with hz1`. Establish `hy1s : ∀ s i, y1 s i = L ^ j * y s i` using `fun s i => rfl`. Establish `hz1s : ∀ s, z1 s = L ^ k • z s - (mat (dual1 W) s *ᵥ v0 - v0)` using `fun s => rfl`.

Establish `hy1Z : y1 ∈ Z1 (Loc.colRep W)` using `Submodule.smul_mem _ _ hy`. Establish `hz1Z : z1 ∈ Z1 (Loc.colRep (dual1 W))` using `Submodule.sub_mem _ (Submodule.smul_mem _ _ hz) (commAlgFunctorCoboundaryZero_mem_cocyclesOne (dual1 W) hc' v0)`. Establish `hy1int : ∀ s i, y1 s i ∈ c2.O` using `fun s i => by rw [hy1s]; exact hc2 (hyint1 s i)`. Establish `hz1int : ∀ s i, z1 s i ∈ c2.O` using `fun s i => by`. Rewrite using `[hz1s, Pi.sub_apply, Pi.sub_apply]`.

Conclude with `sub_mem (hzint2 s i) (sub_mem (CupCob.mulVec_mem c2 _ _ (hW'c2 s) hv0O i) (hv0O i))`. Establish `hz1D : ∀ s ∈ Dec (F` using `ℚ) A, z1 s 1 = 0 := fun s hs => by`. Rewrite using `[hz1s]`. Use `hx s hs` as an intermediate fact. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv0, hup' s hs] at this ⊢`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hy1unr : ∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c2.O) ∧ ∀ s ∈ Ine (F` using `ℚ) B, y1 s = mat W s *ᵥ x - x := by`. Introduce `q hq B hB`. Take `⟨x', hx'O, hx'⟩` from `hyunr1 q hq B hB`.

Conclude with `⟨x', fun i => hc2 (hx'O i), fun s hs => hx' s hs⟩`. Establish `hz1unr : ∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c2.O) ∧ ∀ s ∈ Ine (F` using `ℚ) B, z1 s = mat (dual1 W) s *ᵥ x - x := by`. Introduce `q hq B hB`. Take `⟨x', hx'O, hx'⟩` from `hzunr2 q hq B hB`. Use `⟨x' - v0, fun i => sub_mem (hx'O i) (hv0O i), fun s hs => ?_⟩` and prove the remaining obligations.

Rewrite using `[hz1s, hx' s hs, Matrix.mulVec_sub]`. Normalize the expressions using the abelian group laws. Establish `hy1U : Unr W y1` using `fun w hw => by`. Take `⟨B, hB⟩` from `exists_isPlaceOver Ω w`. Take `⟨x', -, hx'⟩` from `hy1unr w hw B hB`.

Conclude with `⟨B, hB, x', hx'⟩`. Establish `hz1U : Unr (dual1 W) z1` using `fun w hw => by`. Take `⟨B, hB⟩` from `exists_isPlaceOver Ω w`. Take `⟨x', -, hx'⟩` from `hz1unr w hw B hB`. Conclude with `⟨B, hB, x', hx'⟩`.

Take `⟨p, hAp, hlp⟩` from `hW.atL`. Establish `hpS : p ∈ S` using `hW.above p hlp`. Establish `hCobA : ∀ n, Cob2 c2 n (Dec (F` using `ℚ) A) (cup W y1 z1) := fun n => by`. Use `GlobalTheory.T.integralTwoCocycle_reciprocity_trivial_at_last_place hLit l Ω c2 n S (cup W y1 z1) p hW.l_odd hW.above (GlobalTheory.T.cupProductDualTwist_isTwoCocycle_unramified l Ω c2 n S W y1 z1 hc hWc2 hdet2 hW.above hW.unr hy1Z hz1Z hy1int hz1int hy1U hz1U) hpS ?_ A hAp` and prove the remaining obligations. Introduce `v _ hvp`.

Establish `hlv : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal` using `fun h => hvp (place_unique h hlp)`. Take `⟨B, hB⟩` from `exists_isPlaceOver Ω v`. Conclude with `⟨B, hB, GlobalTheory.T.cupProduct_unramifiedClasses_vanishes hLit l Ω c2 n W v B y1 z1 hc hWc2 hdet2 hB hlv (isIntegralCocycleOneModPow_of_integral_cocycle c2 n W _ hy1Z hy1int) (isIntegralCocycleOneModPow_of_integral_cocycle c2 n (dual1 W) _ hz1Z hz1int) (isIntegralCoboundaryOne …`. Establish `hm : Continuous fun s => mat W s` using `Units.continuous_val.comp hc`. Establish `hm' : Continuous fun s => mat (dual1 W) s` using `Units.continuous_val.comp hc'`.

Establish `hloc` using `GlobalTheory.T.local_duality_character_orthogonal_classes hLit l Ω c2 A (fun s => mat W s 1 1) (fun s => mat (dual1 W) s 0 0) (fun s => z1 s 0) (fun s => -y1 s 1) hW.atL (hm.matrix_elem 1 1).continuousOn (hm'.matrix_elem 0 0).continuousOn ((continuous_apply 0).comp hz1Z.1).contin …`. Rewrite using `[galoisRepRankTwoTateDual_matrix_apply W hdet2, det_upper W (hup s hs)]`. Establish `h` using `dt_sq_apply W hdet2 s`. Rewrite `h` using `[det_upper W (hup s hs)]`. Take the linear combination `(eps l s) * h⟩)`.

Use the proof step `(fun s hs t ht => ⟨by rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_two, hup s hs]; ring, by rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_two, hup' t ht]; ring, by`. Rewrite using `[coc_eq W hy1Z s t]`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_two, hup s hs]`. Use the proof step `ring,`. Use `by`.

Rewrite using `[coc_eq (dual1 W) hz1Z s t]`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_two, hz1D t ht]⟩)`. Use the proof step `(nontriv e S A W hW).1 (nontriv e S A W hW).2`. Use the proof step `(fun n => kummerTower_coboundaryTwo_congr (hCobA n) fun s hs t ht => by`. Simplify using `only [cup, om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hz1D t ht, hup' s hs]`.

Use the proof step `ring)`. Break down `hloc with ⟨x', hx'⟩ | ⟨x', hx'⟩` into its components or cases. It suffices to derive a contradiction. Use `hyGr ⟨-x' / L ^ j, fun s hs => ?_⟩` and prove the remaining obligations. Establish `h` using `hx' s hs`.

Simplify using `only [hy1s] at h`. Establish `hLj : L ^ j ≠ 0` using `pow_ne_zero _ hL`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-h`. Establish `hTriv : Triv (dual1 W) A z1` using `⟨![x', 0], fun s hs => by`.

Use extensionality with `i`. Use `fin_cases i`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_two, hx' s hs]`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_two, hup' s hs, hz1D s hs]⟩`. Establish `hB` using `hStr z1 hz1Z hz1U hTriv`.

Establish `hLk : L ^ k ≠ 0` using `pow_ne_zero _ hL`. Establish `e : z = (L ^ k)⁻¹ • (z1 + d0 (Loc.colRep (dual1 W)) v0)`. Rewrite using `[hz1, sub_add_cancel, smul_smul, inv_mul_cancel₀ hLk, one_smul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.add_mem _ hB (LinearMap.mem_range_self _ _))`.
-/
theorem upgrade : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l),
    Nf e S A W → ES W A → StrZero (dual1 W) A → GrZero (dual1 W) A := by
  intro hLit l _ Ω _ _ _ e S A W hW hES hStr z hz hzU hzGr
  obtain ⟨c, y, S', hWc, hy, hyint, hyU, hyGr, -⟩ := hES
  have hdet2 := hW.det2
  have hc := hW.cont
  have hc' : Continuous (dual1 W) := continuous_galoisRepRankTwoTateDual W hdet2 hc
  have hup : ∀ s ∈ Dec (F := ℚ) A, mat W s 1 0 = 0 := hW.upper
  have hup' : ∀ s ∈ Dec (F := ℚ) A, mat (dual1 W) s 1 0 = 0 := fun s hs => by
    rw [galoisRepRankTwoTateDual_matrix_apply W hdet2, hup s hs, mul_zero]

  obtain ⟨c1, j, hc1, hyint1, hyunr1, -, -⟩ := GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S W c y hc hWc hW.unr hy hyU A
  have hWc1 : ∀ s i j, mat W s i j ∈ c1.O := fun s i j => hc1 (hWc s i j)
  have hW'c1 : ∀ s i j, mat (dual1 W) s i j ∈ c1.O := CupCob.dual_representation_integral c1 W hdet2 hWc1
  obtain ⟨c2, k, hc2, hzint2, hzunr2, -, hzgr2⟩ :=
    GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S (dual1 W) c1 z hc' hW'c1 (galoisRepRankTwoTateDual_unramified_outside S W hdet2 hW.above hW.unr) hz hzU A
  obtain ⟨x, hxO, hx⟩ := hzgr2 hzGr
  have hWc2 : ∀ s i j, mat W s i j ∈ c2.O := fun s i j => hc2 (hWc1 s i j)
  have hW'c2 : ∀ s i j, mat (dual1 W) s i j ∈ c2.O := CupCob.dual_representation_integral c2 W hdet2 hWc2
  have hL : ((l : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  set L : Qbar l := ((l : ℕ) : Qbar l) with hLdef
  set v0 : Fin 2 → Qbar l := ![0, x] with hv0
  have hv0O : ∀ i, v0 i ∈ c2.O := fun i => by
    fin_cases i
    · simpa [hv0] using c2.O.zero_mem
    · simpa [hv0] using hxO
  set y1 : G ℚ Ω → Fin 2 → Qbar l := L ^ j • y with hy1
  set z1 : G ℚ Ω → Fin 2 → Qbar l := L ^ k • z - d0 (Loc.colRep (dual1 W)) v0 with hz1
  have hy1s : ∀ s i, y1 s i = L ^ j * y s i := fun s i => rfl
  have hz1s : ∀ s, z1 s = L ^ k • z s - (mat (dual1 W) s *ᵥ v0 - v0) := fun s => rfl
  have hy1Z : y1 ∈ Z1 (Loc.colRep W) := Submodule.smul_mem _ _ hy
  have hz1Z : z1 ∈ Z1 (Loc.colRep (dual1 W)) :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hz) (commAlgFunctorCoboundaryZero_mem_cocyclesOne (dual1 W) hc' v0)
  have hy1int : ∀ s i, y1 s i ∈ c2.O := fun s i => by rw [hy1s]; exact hc2 (hyint1 s i)
  have hz1int : ∀ s i, z1 s i ∈ c2.O := fun s i => by
    rw [hz1s, Pi.sub_apply, Pi.sub_apply]
    exact sub_mem (hzint2 s i) (sub_mem (CupCob.mulVec_mem c2 _ _ (hW'c2 s) hv0O i) (hv0O i))
  have hz1D : ∀ s ∈ Dec (F := ℚ) A, z1 s 1 = 0 := fun s hs => by
    rw [hz1s]
    have := hx s hs
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv0, hup' s hs] at this ⊢
    rw [this]; ring
  have hy1unr : ∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q →
      ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c2.O) ∧ ∀ s ∈ Ine (F := ℚ) B, y1 s = mat W s *ᵥ x - x := by
    intro q hq B hB
    obtain ⟨x', hx'O, hx'⟩ := hyunr1 q hq B hB
    exact ⟨x', fun i => hc2 (hx'O i), fun s hs => hx' s hs⟩
  have hz1unr : ∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q →
      ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c2.O) ∧ ∀ s ∈ Ine (F := ℚ) B, z1 s = mat (dual1 W) s *ᵥ x - x := by
    intro q hq B hB
    obtain ⟨x', hx'O, hx'⟩ := hzunr2 q hq B hB
    refine ⟨x' - v0, fun i => sub_mem (hx'O i) (hv0O i), fun s hs => ?_⟩
    rw [hz1s, hx' s hs, Matrix.mulVec_sub]
    abel
  have hy1U : Unr W y1 := fun w hw => by
    obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
    obtain ⟨x', -, hx'⟩ := hy1unr w hw B hB
    exact ⟨B, hB, x', hx'⟩
  have hz1U : Unr (dual1 W) z1 := fun w hw => by
    obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
    obtain ⟨x', -, hx'⟩ := hz1unr w hw B hB
    exact ⟨B, hB, x', hx'⟩

  obtain ⟨p, hAp, hlp⟩ := hW.atL
  have hpS : p ∈ S := hW.above p hlp
  have hCobA : ∀ n, Cob2 c2 n (Dec (F := ℚ) A) (cup W y1 z1) := fun n => by
    refine GlobalTheory.T.integralTwoCocycle_reciprocity_trivial_at_last_place hLit l Ω c2 n S (cup W y1 z1) p hW.l_odd hW.above
      (GlobalTheory.T.cupProductDualTwist_isTwoCocycle_unramified l Ω c2 n S W y1 z1 hc hWc2 hdet2 hW.above hW.unr hy1Z hz1Z hy1int hz1int hy1U hz1U) hpS ?_ A hAp
    intro v _ hvp
    have hlv : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hvp (place_unique h hlp)
    obtain ⟨B, hB⟩ := exists_isPlaceOver Ω v
    exact ⟨B, hB, GlobalTheory.T.cupProduct_unramifiedClasses_vanishes hLit l Ω c2 n W v B y1 z1 hc hWc2 hdet2 hB hlv
      (isIntegralCocycleOneModPow_of_integral_cocycle c2 n W _ hy1Z hy1int) (isIntegralCocycleOneModPow_of_integral_cocycle c2 n (dual1 W) _ hz1Z hz1int)
      (isIntegralCoboundaryOneModPow_of_integral_vector c2 n W _ (hy1unr v hlv B hB)) (isIntegralCoboundaryOneModPow_of_integral_vector c2 n (dual1 W) _ (hz1unr v hlv B hB))⟩

  have hm : Continuous fun s => mat W s := Units.continuous_val.comp hc
  have hm' : Continuous fun s => mat (dual1 W) s := Units.continuous_val.comp hc'
  have hloc := GlobalTheory.T.local_duality_character_orthogonal_classes hLit l Ω c2 A (fun s => mat W s 1 1) (fun s => mat (dual1 W) s 0 0) (fun s => z1 s 0)
    (fun s => -y1 s 1) hW.atL (hm.matrix_elem 1 1).continuousOn (hm'.matrix_elem 0 0).continuousOn
    ((continuous_apply 0).comp hz1Z.1).continuousOn ((continuous_apply 1).comp hy1Z.1).neg.continuousOn
    (fun s hs => ⟨hWc2 s 1 1, hW'c2 s 0 0, hz1int s 0, neg_mem (hy1int s 1), by
      rw [galoisRepRankTwoTateDual_matrix_apply W hdet2, det_upper W (hup s hs)]
      have h := dt_sq_apply W hdet2 s
      rw [det_upper W (hup s hs)] at h
      linear_combination (eps l s) * h⟩)
    (fun s hs t ht => ⟨by rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_two, hup s hs]; ring,
      by rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_two, hup' t ht]; ring,
      by
        rw [coc_eq W hy1Z s t]
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hup s hs]; ring,
      by
        rw [coc_eq (dual1 W) hz1Z s t]
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hz1D t ht]⟩)
    (nontriv e S A W hW).1 (nontriv e S A W hW).2
    (fun n => kummerTower_coboundaryTwo_congr (hCobA n) fun s hs t ht => by
      simp only [cup, om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hz1D t ht, hup' s hs]; ring)
  rcases hloc with ⟨x', hx'⟩ | ⟨x', hx'⟩
  · exfalso
    refine hyGr ⟨-x' / L ^ j, fun s hs => ?_⟩
    have h := hx' s hs
    simp only [hy1s] at h
    have hLj : L ^ j ≠ 0 := pow_ne_zero _ hL
    field_simp
    linear_combination -h
  · have hTriv : Triv (dual1 W) A z1 := ⟨![x', 0], fun s hs => by
      ext i
      fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hx' s hs]
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hup' s hs, hz1D s hs]⟩
    have hB := hStr z1 hz1Z hz1U hTriv
    have hLk : L ^ k ≠ 0 := pow_ne_zero _ hL
    have e : z = (L ^ k)⁻¹ • (z1 + d0 (Loc.colRep (dual1 W)) v0) := by
      rw [hz1, sub_add_cancel, smul_smul, inv_mul_cancel₀ hLk, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ hB (LinearMap.mem_range_self _ _))

end GlobalTheory.Ord2.Upgrade

end
