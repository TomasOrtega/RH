import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

open Formalism.UG.P

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def oneExc (w : HeightOneSpectrum (𝓞 F)) (a : w.adicCompletion F) : FiniteAdeleRing (𝓞 F) F :=
  afsplitI w a + (1 - afsplitI w 1)

/- English proof (translation)
Rewrite using `[oneExc, afsplit_add_apply, afsplit_sub_apply, afsplitI_self, afsplitI_self, afsplit_one_apply, sub_self, add_zero]`.
-/
theorem oneExc_self (w : HeightOneSpectrum (𝓞 F)) (a : w.adicCompletion F) : oneExc w a w = a := by
  rw [oneExc, afsplit_add_apply, afsplit_sub_apply, afsplitI_self, afsplitI_self, afsplit_one_apply, sub_self, add_zero]

/- English proof (translation)
Rewrite using `[oneExc, afsplit_add_apply, afsplit_sub_apply, afsplitI_ne w w' h, afsplitI_ne w w' h, afsplit_one_apply, sub_zero, zero_add]`.
-/
theorem oneExc_ne (w w' : HeightOneSpectrum (𝓞 F)) (h : w' ≠ w) (a : w.adicCompletion F) : oneExc w a w' = 1 := by
  rw [oneExc, afsplit_add_apply, afsplit_sub_apply, afsplitI_ne w w' h, afsplitI_ne w w' h, afsplit_one_apply, sub_zero,
    zero_add]

/- English proof (translation)
Introduce `w'`. Distinguish the cases in `h : w' = w`. Substitute `h` using the available equality. Rewrite using `[oneExc_self]`. Conclude with `ha`.

Rewrite using `[oneExc_ne w w' h]`. Conclude with `one_mem _`.
-/
theorem oneExc_mem (w : HeightOneSpectrum (𝓞 F)) (a : w.adicCompletion F) (ha : a ∈ w.adicCompletionIntegers F) :
    oneExc w a ∈ intAd F := by
  intro w'
  by_cases h : w' = w
  · subst h; rw [oneExc_self]; exact ha
  · rw [oneExc_ne w w' h]; exact one_mem _

/- English proof (translation)
Take `⟨ι, hι⟩` from `GlobalTheory.TwU.exists_isAdIso F E`. Establish `hca : ((1 : E) ⊗ₜ[F] oneExc w a : AfE F E) ∈ RInt F E` using `Subring.subset_closure (Or.inr ⟨⟨_, oneExc_mem w a ha⟩, rfl⟩)`. Establish `hcb : ((1 : E) ⊗ₜ[F] oneExc w b : AfE F E) ∈ RInt F E` using `Subring.subset_closure (Or.inr ⟨⟨_, oneExc_mem w b hb⟩, rfl⟩)`. Establish `hq : (z - (1 : E) ⊗ₜ[F] oneExc w a) * (z - (1 : E) ⊗ₜ[F] oneExc w b) = 0`. Use `afsplit_inj _ fun w' => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_sub, map_sub, afsplit_prV_tmul, afsplit_prV_tmul]`. Distinguish the cases in `h : w' = w`. Substitute `h` using the available equality. Rewrite using `[oneExc_self, oneExc_self]`. Conclude with `hv`.

Rewrite using `[oneExc_ne w w' h, oneExc_ne w w' h, hoff w' h, ← Algebra.TensorProduct.one_def, sub_self, zero_mul]`. Rewrite using `[hι.2]`. Introduce `P`. Establish `h1` using `congrArg (fun x => ι x P) hq`. Simplify using `only [map_mul, map_sub, map_zero] at h1`.

Establish `h2 : (ι z P - ι ((1 : E) ⊗ₜ[F] oneExc w a) P) * (ι z P - ι ((1 : E) ⊗ₜ[F] oneExc w b) P) = 0` using `h1`. Break down `mul_eq_zero.1 h2 with h | h` into its components or cases. Rewrite using `[sub_eq_zero.1 h]`. Conclude with `(hι.2 _).1 hca P`. Rewrite using `[sub_eq_zero.1 h]`.

Conclude with `(hι.2 _).1 hcb P`.
-/
theorem mem_RInt_of_quad (z : AfE F E) (w : HeightOneSpectrum (𝓞 F)) (a b : w.adicCompletion F)
    (ha : a ∈ w.adicCompletionIntegers F) (hb : b ∈ w.adicCompletionIntegers F)
    (hoff : ∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → prV (E := E) w' z = 1)
    (hv : (prV (E := E) w z - (1 : E) ⊗ₜ[F] a) * (prV (E := E) w z - (1 : E) ⊗ₜ[F] b) = 0) :
    z ∈ RInt F E := by
  obtain ⟨ι, hι⟩ := GlobalTheory.TwU.exists_isAdIso F E
  have hca : ((1 : E) ⊗ₜ[F] oneExc w a : AfE F E) ∈ RInt F E :=
    Subring.subset_closure (Or.inr ⟨⟨_, oneExc_mem w a ha⟩, rfl⟩)
  have hcb : ((1 : E) ⊗ₜ[F] oneExc w b : AfE F E) ∈ RInt F E :=
    Subring.subset_closure (Or.inr ⟨⟨_, oneExc_mem w b hb⟩, rfl⟩)
  have hq : (z - (1 : E) ⊗ₜ[F] oneExc w a) * (z - (1 : E) ⊗ₜ[F] oneExc w b) = 0 := by
    refine afsplit_inj _ fun w' => ?_
    rw [map_mul, map_sub, map_sub, afsplit_prV_tmul, afsplit_prV_tmul]
    by_cases h : w' = w
    · subst h
      rw [oneExc_self, oneExc_self]
      exact hv
    · rw [oneExc_ne w w' h, oneExc_ne w w' h, hoff w' h, ← Algebra.TensorProduct.one_def, sub_self, zero_mul]
  rw [hι.2]
  intro P
  have h1 := congrArg (fun x => ι x P) hq
  simp only [map_mul, map_sub, map_zero] at h1
  have h2 : (ι z P - ι ((1 : E) ⊗ₜ[F] oneExc w a) P) * (ι z P - ι ((1 : E) ⊗ₜ[F] oneExc w b) P) = 0 := h1
  rcases mul_eq_zero.1 h2 with h | h
  · rw [sub_eq_zero.1 h]; exact (hι.2 _).1 hca P
  · rw [sub_eq_zero.1 h]; exact (hι.2 _).1 hcb P

end SlopeTestRemainingChoices

section Main

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n p G A J _ hG hI hS v y hy hoff hord`. Use `set w := (A.pl v).1 with hw`. Use `set s := A.spl v (prV (E := E) w (y : AfE F E)) with hs_def`. Establish `hy1 : (y : AfE F E) * sigR σ (FiniteAdeleRing (𝓞 F) F) (y : AfE F E) = 1`. Establish `h` using `congrArg Units.val (MonoidHom.mem_ker.1 hy)`.

Conclude with `h`. Establish `hprod : prV (E` using `E) w (y : AfE F E) * sigR σ (w.adicCompletion F) (prV (E := E) w (y : AfE F E)) = 1 := by`. Establish `h` using `congrArg (prV (E := E) w) hy1`. Rewrite `h` using `[map_mul, map_one]`. Rewrite using `[← h]`.

Use `congr 1`. Conclude with `(DFunLike.congr_fun (afsplit_prV_comp_sigR σ w) _).symm`. Establish `hss : s.1 * s.2 = 1`. Establish `h` using `congrArg (A.spl v) hprod`. Rewrite `h` using `[map_mul, hG.sig v, map_one]`.

Conclude with `congrArg Prod.fst h`. Establish `hss' : s.2 * s.1 = 1` using `by rw [mul_comm]; exact hss`. Establish `hset` using `G.P.setting v`. Use `haveI := hset.frac_alt`. Establish `hp` using `hset.p_unif`.

Use `set x : G.P.Qq v := (A.eQ v).symm s.1 with hx_def`. Establish `hxe : A.eQ v x = s.1` using `RingEquiv.apply_symm_apply _ _`. Establish `hx0 : x ≠ 0`. Introduce `h0`. Rewrite `hxe` using `[h0, map_zero]`.

Rewrite `hss` using `[← hxe, zero_mul]`. Conclude with `zero_ne_one hss`. Take `⟨k, u, hu⟩` from `exists_eq_unit_mul_zpow₂ hp hx0`. Establish `hk : k = 0`. Establish `h1 : ordA A v y = ordP (G.P.W v) p x` using `rfl`.

Rewrite `hord` using `[h1, hu, ordP_eq hp]`. Conclude with `hord`. Substitute `hk` using the available equality. Rewrite `hu` using `[zpow_zero, mul_one]`. Establish `ha : s.1 ∈ w.adicCompletionIntegers F`.

Rewrite using `[← hxe]`. Conclude with `(hI v x).1 ⟨u, hu.symm⟩`. Establish `hb : s.2 ∈ w.adicCompletionIntegers F`. Establish `h2 : s.2 = A.eQ v x⁻¹`. Rewrite using `[map_inv₀, hxe]`.

Conclude with `eq_inv_of_mul_eq_one_right hss`. Rewrite using `[h2]`. Use `(hI v x⁻¹).1 ⟨(u⁻¹ : (G.P.W v)ˣ), ?_⟩` and prove the remaining obligations. Rewrite using `[hu]`. Conclude with `map_units_inv (algebraMap (G.P.W v) (G.P.Qq v) : G.P.W v →* G.P.Qq v) u`.

Establish `key : ∀ t : E ⊗[F] w.adicCompletion F, ((A.spl v t).1 - s.1) * ((A.spl v t).1 - s.2) = 0 → ((A.spl v t).2 - s.1) * ((A.spl v t).2 - s.2) = 0 → (t - (1 : E) ⊗ₜ[F] s.1) * (t - (1 : E) ⊗ₜ[F] s.2) = 0`. Introduce `t h1 h2`. Apply `(A.spl v).injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_sub, map_sub, hS v, hS v, map_zero]`. Conclude with `Prod.ext h1 h2`.

Establish `hyR : (y : AfE F E) ∈ RInt F E`. Use `mem_RInt_of_quad _ w s.1 s.2 ha hb hoff (key _ ?_ ?_)` and prove the remaining obligations. Use `show (s.1 - s.1) * (s.1 - s.2) = 0`. Rewrite using `[sub_self, zero_mul]`. Use `show (s.2 - s.1) * (s.2 - s.2) = 0`.

Rewrite using `[sub_self, mul_zero]`. Establish `hinv : ∀ w' : HeightOneSpectrum (𝓞 F), prV (E` using `E) w' ((y⁻¹ : (AfE F E)ˣ) : AfE F E) * prV (E := E) w' (y : AfE F E) = 1 := by`. Introduce `w'`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Use `set t := A.spl v (prV (E := E) w ((y⁻¹ : (AfE F E)ˣ) : AfE F E)) with ht_def`.

Establish `hts : t * s = 1` using `by rw [ht_def, hs_def, ← map_mul, hinv w, map_one]`. Establish `ht1 : t.1 = s.2`. Establish `h : t.1 * s.1 = 1` using `congrArg Prod.fst hts`. Combine the equalities or inequalities in the displayed calculation. Establish `ht2 : t.2 = s.1`.

Establish `h : t.2 * s.2 = 1` using `congrArg Prod.snd hts`. Combine the equalities or inequalities in the displayed calculation. Establish `hyR' : ((y⁻¹ : (AfE F E)ˣ) : AfE F E) ∈ RInt F E`. Use `mem_RInt_of_quad _ w s.1 s.2 ha hb (fun w' h => ?_) (key _ ?_ ?_)` and prove the remaining obligations. Establish `h3` using `hinv w'`.

Rewrite `h3` using `[hoff w' h, mul_one]`. Then use the resulting hypothesis. Use `show (t.1 - s.1) * (t.1 - s.2) = 0`. Rewrite using `[ht1, sub_self, mul_zero]`. Use `show (t.2 - s.1) * (t.2 - s.2) = 0`. Rewrite using `[ht2, sub_self, zero_mul]`.

Conclude with `(Submonoid.mem_units_iff _ _).2 ⟨hyR, hyR'⟩`.
-/
theorem mem_intU_of_oneOff_ordA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) [Fact p.Prime], LocGood σ J A → LocInt A →
    SplAlg A → ∀ v, ∀ y ∈ U1 σ, OneOff (A.pl v).1 y → ordA A v y = 0 → y ∈ intU F E := by
  intro F E _ _ _ _ _ σ n p G A J _ hG hI hS v y hy hoff hord
  set w := (A.pl v).1 with hw
  set s := A.spl v (prV (E := E) w (y : AfE F E)) with hs_def
  have hy1 : (y : AfE F E) * sigR σ (FiniteAdeleRing (𝓞 F) F) (y : AfE F E) = 1 := by
    have h := congrArg Units.val (MonoidHom.mem_ker.1 hy)
    exact h
  have hprod : prV (E := E) w (y : AfE F E) * sigR σ (w.adicCompletion F) (prV (E := E) w (y : AfE F E)) = 1 := by
    have h := congrArg (prV (E := E) w) hy1
    rw [map_mul, map_one] at h
    rw [← h]
    congr 1
    exact (DFunLike.congr_fun (afsplit_prV_comp_sigR σ w) _).symm
  have hss : s.1 * s.2 = 1 := by
    have h := congrArg (A.spl v) hprod
    rw [map_mul, hG.sig v, map_one] at h
    exact congrArg Prod.fst h
  have hss' : s.2 * s.1 = 1 := by rw [mul_comm]; exact hss
  have hset := G.P.setting v
  haveI := hset.frac_alt
  have hp := hset.p_unif
  set x : G.P.Qq v := (A.eQ v).symm s.1 with hx_def
  have hxe : A.eQ v x = s.1 := RingEquiv.apply_symm_apply _ _
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hxe
    rw [← hxe, zero_mul] at hss
    exact zero_ne_one hss
  obtain ⟨k, u, hu⟩ := exists_eq_unit_mul_zpow₂ hp hx0
  have hk : k = 0 := by
    have h1 : ordA A v y = ordP (G.P.W v) p x := rfl
    rw [h1, hu, ordP_eq hp] at hord
    exact hord
  subst hk
  rw [zpow_zero, mul_one] at hu
  have ha : s.1 ∈ w.adicCompletionIntegers F := by
    rw [← hxe]
    exact (hI v x).1 ⟨u, hu.symm⟩
  have hb : s.2 ∈ w.adicCompletionIntegers F := by
    have h2 : s.2 = A.eQ v x⁻¹ := by
      rw [map_inv₀, hxe]
      exact eq_inv_of_mul_eq_one_right hss
    rw [h2]
    refine (hI v x⁻¹).1 ⟨(u⁻¹ : (G.P.W v)ˣ), ?_⟩
    rw [hu]
    exact map_units_inv (algebraMap (G.P.W v) (G.P.Qq v) : G.P.W v →* G.P.Qq v) u
  have key : ∀ t : E ⊗[F] w.adicCompletion F, ((A.spl v t).1 - s.1) * ((A.spl v t).1 - s.2) = 0 →
      ((A.spl v t).2 - s.1) * ((A.spl v t).2 - s.2) = 0 →
      (t - (1 : E) ⊗ₜ[F] s.1) * (t - (1 : E) ⊗ₜ[F] s.2) = 0 := by
    intro t h1 h2
    apply (A.spl v).injective
    rw [map_mul, map_sub, map_sub, hS v, hS v, map_zero]
    exact Prod.ext h1 h2
  have hyR : (y : AfE F E) ∈ RInt F E := by
    refine mem_RInt_of_quad _ w s.1 s.2 ha hb hoff (key _ ?_ ?_)
    · show (s.1 - s.1) * (s.1 - s.2) = 0
      rw [sub_self, zero_mul]
    · show (s.2 - s.1) * (s.2 - s.2) = 0
      rw [sub_self, mul_zero]
  have hinv : ∀ w' : HeightOneSpectrum (𝓞 F),
      prV (E := E) w' ((y⁻¹ : (AfE F E)ˣ) : AfE F E) * prV (E := E) w' (y : AfE F E) = 1 := by
    intro w'
    rw [← map_mul, Units.inv_mul, map_one]
  set t := A.spl v (prV (E := E) w ((y⁻¹ : (AfE F E)ˣ) : AfE F E)) with ht_def
  have hts : t * s = 1 := by rw [ht_def, hs_def, ← map_mul, hinv w, map_one]
  have ht1 : t.1 = s.2 := by
    have h : t.1 * s.1 = 1 := congrArg Prod.fst hts
    calc t.1 = t.1 * (s.1 * s.2) := by rw [hss, mul_one]
      _ = (t.1 * s.1) * s.2 := (mul_assoc _ _ _).symm
      _ = s.2 := by rw [h, one_mul]
  have ht2 : t.2 = s.1 := by
    have h : t.2 * s.2 = 1 := congrArg Prod.snd hts
    calc t.2 = t.2 * (s.2 * s.1) := by rw [hss', mul_one]
      _ = (t.2 * s.2) * s.1 := (mul_assoc _ _ _).symm
      _ = s.1 := by rw [h, one_mul]
  have hyR' : ((y⁻¹ : (AfE F E)ˣ) : AfE F E) ∈ RInt F E := by
    refine mem_RInt_of_quad _ w s.1 s.2 ha hb (fun w' h => ?_) (key _ ?_ ?_)
    · have h3 := hinv w'
      rwa [hoff w' h, mul_one] at h3
    · show (t.1 - s.1) * (t.1 - s.2) = 0
      rw [ht1, sub_self, mul_zero]
    · show (t.2 - s.1) * (t.2 - s.2) = 0
      rw [ht2, sub_self, zero_mul]
  exact (Submonoid.mem_units_iff _ _).2 ⟨hyR, hyR'⟩

end Main

end GlobalTheory.TwV.Xc

end
