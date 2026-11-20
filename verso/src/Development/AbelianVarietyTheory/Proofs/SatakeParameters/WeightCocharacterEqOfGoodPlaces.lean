import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdjoinSplitHeckeGeneratorsDualsSphericalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatumStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeConjPlaceEqDualLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCommonEigenvalueOfMemAdjoin

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.LabDet

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin`. Consider the case `exact _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin`. Consider the case `(apply _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin ..)`.
-/
theorem adjoin_common {M : Type} [AddCommGroup M] [Module ℂ M] (s : Set (Module.End ℂ M)) (u u' : M)
    (h : ∀ x ∈ s, ∃ l : ℂ, x u = l • u ∧ x u' = l • u') :
    ∀ a ∈ Algebra.adjoin ℂ s, ∃ l : ℂ, a u = l • u ∧ a u' = l • u' := by
  first
  | exact @_root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin
  | exact _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin
  | (apply _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin ..)

variable {D : D7}

/- English proof (translation)
Unfold `opOf`. Rewrite using `[Finsupp.sum_single_index (by simp), one_smul]`.
-/
theorem opOf_single {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (d : List ℤ) : opOf π P (Finsupp.single d 1) = ∑ γ ∈ rep V P d, π γ := by
  unfold opOf
  rw [Finsupp.sum_single_index (by simp), one_smul]

/- English proof (translation)
Rewrite using `[opOf_single]`. Unfold `rep`. Rewrite using `[dif_neg h, Finset.sum_empty]`.
-/
theorem opOf_single_of_not {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (d : List ℤ) (h : ¬ IsLab V P d) : opOf π P (Finsupp.single d 1) = 0 := by
  rw [opOf_single]
  unfold rep
  rw [dif_neg h, Finset.sum_empty]

/- English proof (translation)
Unfold `rep`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem sphOp_rep {V : HSp D} {P : Pl D.host.E} {d : List ℤ} (h : IsLab V P d) : SphOp V P d (rep V P d) := by
  unfold rep
  rw [dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Introduce `d hd`. Take `⟨x, hx, hxe⟩` from `GlobalTheory.T.exists_adjoin_splitHeckeGenerators_duals_spherical V P hP M π d`. Take `⟨l, h1, h2⟩` from `adjoin_common _ u u' (by`. Introduce and unpack `y ⟨k, hk, rfl | rfl⟩`. Distinguish the cases in `hl : IsLab V P (splitLab V.rank k)`.

Conclude with `⟨_, ha _ hl, by rw [ha' _ hl, ea k hk]⟩`. Conclude with `⟨0, by simp [opOf_single_of_not π P _ hl], by simp [opOf_single_of_not π P _ hl]⟩`. Establish `hc` using `(GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel V P).2.2 (Finsupp.single (splitLab V.rank k) 1) M π`. Establish `hd : dualC (Finsupp.single (splitLab V.rank k) 1) = Finsupp.single (dualLab (splitLab V.rank k)) 1`. Unfold `dualC`.

Rewrite using `[Finsupp.mapDomain_single]`. Rewrite `hc` using `[hd]`. Rewrite using `[← hc u fu, ← hc u' fu']`. Distinguish the cases in `hl : IsLab V (conjPl P) (splitLab V.rank k)`. Conclude with `⟨_, hb _ hl, by rw [hb' _ hl, eb k hk]⟩`.

Conclude with `⟨0, by simp [opOf_single_of_not π _ _ hl], by simp [opOf_single_of_not π _ _ hl]⟩) x hx`. Rewrite `h1` using `[hxe u fu, ha d hd]`. Rewrite `h2` using `[hxe u' fu', ha' d hd]`. Rewrite using `[smul_left_injective ℂ hu h1, smul_left_injective ℂ hu' h2]`.
-/
theorem eq_of_split {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (hP : conjPl P ≠ P) (u u' : M) (hu : u ≠ 0) (hu' : u' ≠ 0) (fu : ∀ k ∈ hyp V P, π k u = u) (fu' : ∀ k ∈ hyp V P, π k u' = u')
    (a a' b b' : List ℤ → ℂ)
    (ha : ∀ d, IsLab V P d → opOf π P (Finsupp.single d 1) u = a d • u)
    (ha' : ∀ d, IsLab V P d → opOf π P (Finsupp.single d 1) u' = a' d • u')
    (hb : ∀ d, IsLab V (conjPl P) d → opOf π (conjPl P) (Finsupp.single d 1) u = b d • u)
    (hb' : ∀ d, IsLab V (conjPl P) d → opOf π (conjPl P) (Finsupp.single d 1) u' = b' d • u')
    (ea : ∀ k, k ≤ V.rank → a (splitLab V.rank k) = a' (splitLab V.rank k))
    (eb : ∀ k, k ≤ V.rank → b (splitLab V.rank k) = b' (splitLab V.rank k)) :
    ∀ d, IsLab V P d → a d = a' d := by
  intro d hd
  obtain ⟨x, hx, hxe⟩ := GlobalTheory.T.exists_adjoin_splitHeckeGenerators_duals_spherical V P hP M π d
  obtain ⟨l, h1, h2⟩ := adjoin_common _ u u' (by
    rintro y ⟨k, hk, rfl | rfl⟩
    · by_cases hl : IsLab V P (splitLab V.rank k)
      · exact ⟨_, ha _ hl, by rw [ha' _ hl, ea k hk]⟩
      · exact ⟨0, by simp [opOf_single_of_not π P _ hl], by simp [opOf_single_of_not π P _ hl]⟩
    · have hc := (GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel V P).2.2 (Finsupp.single (splitLab V.rank k) 1) M π
      have hd : dualC (Finsupp.single (splitLab V.rank k) 1) = Finsupp.single (dualLab (splitLab V.rank k)) 1 := by
        unfold dualC
        rw [Finsupp.mapDomain_single]
      rw [hd] at hc
      rw [← hc u fu, ← hc u' fu']
      by_cases hl : IsLab V (conjPl P) (splitLab V.rank k)
      · exact ⟨_, hb _ hl, by rw [hb' _ hl, eb k hk]⟩
      · exact ⟨0, by simp [opOf_single_of_not π _ _ hl], by simp [opOf_single_of_not π _ _ hl]⟩) x hx
  rw [hxe u fu, ha d hd] at h1
  rw [hxe u' fu', ha' d hd] at h2
  rw [smul_left_injective ℂ hu h1, smul_left_injective ℂ hu' h2]

def rLin (V : HSp D) (g : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun F := fun h => F (h * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rRep {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : GA D V →* Module.End ℂ (MMap M) where
  toFun g := postOn M (rLin V g)
  map_one' := by
    ext U v h
    show U v (h * 1) = U v h
    rw [mul_one]
  map_mul' g g' := by
    ext U v h
    show U v (h * (g * g')) = U v (h * g * g')
    rw [mul_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rRep_apply {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (g : GA D V) (U : MMap M) (v : M.Vec) (h : GA D V) :
    rRep M g U v h = U v (h * g) := rfl

/- English proof (translation)
Use extensionality with `U v h`. Rewrite using `[LinearMap.sum_apply, MultilinearMap.sum_apply, Finset.sum_apply]`. Both sides reduce to the same expression.
-/
theorem sum_rRep {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (B : Finset (GA D V)) :
    ∑ γ ∈ B, rRep M γ = heckeOn M B := by
  ext U v h
  rw [LinearMap.sum_apply, MultilinearMap.sum_apply, Finset.sum_apply]
  rfl

/- English proof (translation)
Proceed by induction on `hU using Submodule.span_induction with`. Consider the case `mem x hx`. Use extensionality with `v h`. Rewrite using `[rRep_apply, hx.lev v k hk h, h1, one_mul]`. Consider the case `zero => exact map_zero _`.

Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy]`. Consider the case `smul a x _ hx => rw [map_smul, hx]`.
-/
theorem mult_lev {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (U : MMap M) (hU : U ∈ Mult θ M J χ) (k : GA D V) (hk : k ∈ J)
    (h1 : χ k = 1) : rRep M k U = U := by
  induction hU using Submodule.span_induction with
  | mem x hx =>
    ext v h
    rw [rRep_apply, hx.lev v k hk h, h1, one_mul]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

/- English proof (translation)
Unfold `partFull`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`.
-/
theorem mem_partFull {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : Pl D.host.E → List ℤ → ℂ) (U : MMap M) :
    U ∈ partFull θ M J χ Sb c ↔ U ∈ Mult θ M J χ ∧ ∀ P d B, Hecke₂ V J χ Sb P d B → heckeOn M B U = c P d • U := by
  unfold partFull
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF i c c' hc hc' hs hi`. Take `⟨hQ, hgood, hoff, -⟩` from `GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev`. Take `⟨n, hβ⟩` from `hC.lev.βW i`. Establish `hlev` using `fun (P : Pl D.host.E) (hP : Good R A.μ0 P) => GlobalTheory.T.level_operators_at_prime_off_level_datum (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top) (by`. Introduce `PP hPP`.

Use `hP PP (hPP.imp id ?_)` and prove the remaining obligations. Introduce `h`. Conclude with `absurd h (Finset.notMem_empty _))`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hc`. Take `⟨x', hx', hx0'⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hc'`.

Establish `inj : Function.Injective (R.HW i (sg0 D A)).e` using `(hC.models.HW i (sg0 D A)).1`. Establish `hu : (R.HW i (sg0 D A)).e x ≠ 0` using `fun h => hx0 (inj (by rw [h, map_zero]))`. Establish `hu' : (R.HW i (sg0 D A)).e x' ≠ 0` using `fun h => hx0' (inj (by rw [h, map_zero]))`. Establish `hp` using `(mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_inf.1 (Submodule.mem_comap.1 hx)).2`. Establish `hp'` using `(mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_inf.1 (Submodule.mem_comap.1 hx')).2`.

Establish `key : ∀ P, Good R A.μ0 P → ∀ d, IsLab (Wc D i) P d → c P d = c' P d`. Introduce `P hP`. Distinguish the cases in `hcP : conjPl P = P`. Conclude with `fun d hd => hi P d hP hcP hd`. Establish `hP' : Good R A.μ0 (conjPl P)` using `(hgood _ P hP).2.1`.

Establish `hcc : conjPl (conjPl P) = P` using `ValuationRepresentative.conjPl_conjPl P`. Use `eq_of_split (rRep (R.MW i (sg0 D A))) P hcP _ _ hu hu' ?_ ?_ (c P) (c' P) (c (conjPl P)) (c' (conjPl P)) ?_ ?_ ?_ ?_ (hs P hP hcP) (hs _ hP' (by rw [hcc]; exact fun h => hcP h.symm))` and prove the remaining obligations. Conclude with `fun k hk => mult_lev _ _ _ _ _ hp.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2`. Conclude with `fun k hk => mult_lev _ _ _ _ _ hp'.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2`. Introduce `d hd`.

Rewrite using `[opOf_single, sum_rRep]`. Conclude with `hp.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩)`. Introduce `d hd`. Rewrite using `[opOf_single, sum_rRep]`. Conclude with `hp'.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩)`.

Introduce `d hd`. Rewrite using `[opOf_single, sum_rRep]`. Conclude with `hp.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩)`. Introduce `d hd`. Rewrite using `[opOf_single, sum_rRep]`.

Conclude with `hp'.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩)`. Establish `key2 : ∀ P d B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF P d B → c P d = c' P d`. Introduce `P d B hB`. Establish `hP : Good R A.μ0 P`. Take `⟨_, _, _, _, ho, _⟩` from `hB`.

Conclude with `(hoff SF hSF P).1 ho`. Conclude with `key P hP d ⟨B, (((hlev P hP).2.1 SF d B).1 hB).2⟩`. Unfold `Wcc`. Use `congr 2`. Use extensionality with `U`.

Rewrite using `[mem_partFull, mem_partFull]`. Use `and_congr_right fun _ => forall_congr' fun P => forall_congr' fun d => forall_congr' fun B => imp_congr_right fun hB => ?_` and prove the remaining obligations. Rewrite using `[key2 P d B hB]`.
-/
theorem part_eq_of_labels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ SF, IsSF R SF → ∀ i (c c' : Pl D.host.E → List ℤ → ℂ), Wcc R SF i c ≠ ⊥ → Wcc R SF i c' ≠ ⊥ → (∀ P, Good R A.μ0 P → conjPl P ≠ P → ∀ k, k ≤ (Wc D i).rank → c P (splitLab (Wc D i).rank k) = c' P (splitLab (Wc D i).rank k)) → (∀ P d, Good R A.μ0 P → conjPl P = P → IsLab (Wc D i) P d → c P d = c' P d) → Wcc R SF i c = Wcc R SF i c' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF i c c' hc hc' hs hi
  obtain ⟨hQ, hgood, hoff, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  obtain ⟨n, hβ⟩ := hC.lev.βW i
  have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
    GlobalTheory.T.level_operators_at_prime_off_level_datum (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P
      (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
      (by
        intro PP hPP
        refine hP PP (hPP.imp id ?_)
        intro h
        exact absurd h (Finset.notMem_empty _))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  obtain ⟨x', hx', hx0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc'
  have inj : Function.Injective (R.HW i (sg0 D A)).e := (hC.models.HW i (sg0 D A)).1
  have hu : (R.HW i (sg0 D A)).e x ≠ 0 := fun h => hx0 (inj (by rw [h, map_zero]))
  have hu' : (R.HW i (sg0 D A)).e x' ≠ 0 := fun h => hx0' (inj (by rw [h, map_zero]))
  have hp := (mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_inf.1 (Submodule.mem_comap.1 hx)).2
  have hp' := (mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_inf.1 (Submodule.mem_comap.1 hx')).2
  have key : ∀ P, Good R A.μ0 P → ∀ d, IsLab (Wc D i) P d → c P d = c' P d := by
    intro P hP
    by_cases hcP : conjPl P = P
    · exact fun d hd => hi P d hP hcP hd
    · have hP' : Good R A.μ0 (conjPl P) := (hgood _ P hP).2.1
      have hcc : conjPl (conjPl P) = P := ValuationRepresentative.conjPl_conjPl P
      refine eq_of_split (rRep (R.MW i (sg0 D A))) P hcP _ _ hu hu' ?_ ?_ (c P) (c' P) (c (conjPl P)) (c' (conjPl P)) ?_ ?_ ?_ ?_
        (hs P hP hcP) (hs _ hP' (by rw [hcc]; exact fun h => hcP h.symm))
      · exact fun k hk => mult_lev _ _ _ _ _ hp.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2
      · exact fun k hk => mult_lev _ _ _ _ _ hp'.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2
      · intro d hd
        rw [opOf_single, sum_rRep]
        exact hp.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩)
      · intro d hd
        rw [opOf_single, sum_rRep]
        exact hp'.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩)
      · intro d hd
        rw [opOf_single, sum_rRep]
        exact hp.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩)
      · intro d hd
        rw [opOf_single, sum_rRep]
        exact hp'.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩)
  have key2 : ∀ P d B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF P d B →
      c P d = c' P d := by
    intro P d B hB
    have hP : Good R A.μ0 P := by
      obtain ⟨_, _, _, _, ho, _⟩ := hB
      exact (hoff SF hSF P).1 ho
    exact key P hP d ⟨B, (((hlev P hP).2.1 SF d B).1 hB).2⟩
  unfold Wcc
  congr 2
  ext U
  rw [mem_partFull, mem_partFull]
  refine and_congr_right fun _ => forall_congr' fun P => forall_congr' fun d => forall_congr' fun B => imp_congr_right fun hB => ?_
  rw [key2 P d B hB]

end GlobalTheory.Hk3.LabDet

end
