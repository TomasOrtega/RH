import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperSectionSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotAddSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotDevissageSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MulQuotEqSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionNonvanishSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionMulInjSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperSectionObj
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapper
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PIdealTwistFamily
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutZeroNotLe
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeAway
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace SnapperSections

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

/- English proof (translation)
The claim follows from `| 0, _, _, I => by simp [SubSystem.twistPows] | t + 1, L, n, I => by rw [SubSystem.twistPows, SubSystem.twist_sub_eq_mul_of_line, SubSystem.pow_sub, twistPows_sub F t, Fin.prod_univ_castSucc] ring`.
-/
theorem twistPows_sub (F : SubSystem k x Ω) : ∀ (t : ℕ) (L : Fin t → SubSystem k x Ω) (n : Fin t → ℕ)
    (I : Chart x), (F.twistPows t L n).sub I = F.sub I * ∏ j, (L j).sub I ^ n j
  | 0, _, _, I => by simp [SubSystem.twistPows]
  | t + 1, L, n, I => by
    rw [SubSystem.twistPows, SubSystem.twist_sub_eq_mul_of_line, SubSystem.pow_sub, twistPows_sub F t,
      Fin.prod_univ_castSucc]
    ring

def powsBundle (F : LineBundle k x) : (t : ℕ) → (Fin t → LineBundle k x) → (Fin t → ℕ) → LineBundle k x
  | 0, _, _ => F
  | t + 1, L, n => (powsBundle F t (fun j => L j.castSucc) (fun j => n j.castSucc)).tensorProd
      ((L (Fin.last t)).powBundle (n (Fin.last t)))

/- English proof (translation)
The claim follows from `SubSystem.twist_sub_eq_mul_of_line _ _ I`.
-/
theorem tensorProd_sub (P Q : LineBundle k x) (I : Chart x) :
    (P.tensorProd Q).sub I = Q.sub I * P.sub I :=
  SubSystem.twist_sub_eq_mul_of_line _ _ I

/- English proof (translation)
The claim follows from `| 0, _, _, I => by simp [powsBundle] | t + 1, L, n, I => by rw [powsBundle, tensorProd_sub, LineBundle.powBundle_toSubSystem, SubSystem.pow_sub, powsBundle_sub F t, Fin.prod_univ_castSucc] ring`.
-/
theorem powsBundle_sub (F : LineBundle k x) : ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ)
    (I : Chart x), (powsBundle F t L n).sub I = F.sub I * ∏ j, (L j).sub I ^ n j
  | 0, _, _, I => by simp [powsBundle]
  | t + 1, L, n, I => by
    rw [powsBundle, tensorProd_sub, LineBundle.powBundle_toSubSystem, SubSystem.pow_sub, powsBundle_sub F t,
      Fin.prod_univ_castSucc]
    ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twistBundle_sub (c : ℤ) (I : Chart x) : (twistBundle k x c).sub I = (twistSys k x c).sub I := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem idealSys_sub (pp : Ideal (Poly k N)) (I : Chart x) : (idealSys x pp).sub I = idealMod (x := x) pp I := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem supFam_sub {F G : SubFamily k x Ω} (I : Chart x) : (F.sup G).sub I = F.sub I ⊔ G.sub I := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem spanBundle_sub (s : Ω) (hs : s ≠ 0) (I : Chart x) :
    (spanBundle k x s hs).sub I = Submodule.span (chartRing k x I) {s} := rfl

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[pow_succ]`. Simplify using `[h]`.

Use `_ = (∏ i, a i ^ n i) * a j := by rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']; simp`.
-/
theorem prod_update_pow {M : Type*} [CommMonoid M] {t : ℕ} (a : Fin t → M) (n : Fin t → ℕ) (j : Fin t) :
    ∏ i, a i ^ Function.update n j (n j + 1) i = (∏ i, a i ^ n i) * a j := by
  calc ∏ i, a i ^ Function.update n j (n j + 1) i = ∏ i, (a i ^ n i * if i = j then a j else 1) :=
        Finset.prod_congr rfl fun i _ => by
          by_cases h : i = j
          · subst h
            simp [pow_succ]
          · simp [h]
    _ = (∏ i, a i ^ n i) * a j := by rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']; simp

/- English proof (translation)
The claim follows from `Submodule.mul_le.mpr fun _ hp _ hq => Submodule.mul_mem_mul (h₁ hp) (h₂ hq)`.
-/
theorem mul_le_mul_sub {I : Chart x} {P Q P' Q' : Submodule (chartRing k x I) Ω} (h₁ : P ≤ P') (h₂ : Q ≤ Q') :
    P * Q ≤ P' * Q' :=
  Submodule.mul_le.mpr fun _ hp _ hq => Submodule.mul_mem_mul (h₁ hp) (h₂ hq)

/- English proof (translation)
Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, m, e, -, hm, hf, hme, rfl⟩`. Conclude with `Submodule.mem_one.mpr ⟨⟨_, f, m, e, hm, hf, hme, rfl⟩, rfl⟩`.
-/
theorem idealMod_le_one (pp : Ideal (Poly k N)) (I : Chart x) : idealMod (x := x) pp I ≤ 1 := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, m, e, -, hm, hf, hme, rfl⟩
  exact Submodule.mem_one.mpr ⟨⟨_, f, m, e, hm, hf, hme, rfl⟩, rfl⟩

attribute [local instance] MvPolynomial.gradedAlgebra in

/- English proof (translation)
Establish `hJ : (zeroIdeal D s).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k)` using `Ideal.homogeneous_span _ _ fun f ⟨c, hf, _⟩ => ⟨c, (mem_homogeneousSubmodule c f).mpr hf⟩`. Introduce `f hf d`. Establish `h` using `hJ d hf`. Establish `hc : (DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) k) f d : Poly k N) = homogeneousComponent d f` using `decomposition.decompose'_apply f d`. Rewrite `h` using `[hc]`. Then use the resulting hypothesis.
-/
theorem zeroIdeal_homog (D : SubSystem k x Ω) (s : Ω) :
    ∀ f ∈ zeroIdeal D s, ∀ d : ℕ, homogeneousComponent d f ∈ zeroIdeal D s := by
  have hJ : (zeroIdeal D s).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) :=
    Ideal.homogeneous_span _ _ fun f ⟨c, hf, _⟩ => ⟨c, (mem_homogeneousSubmodule c f).mpr hf⟩
  intro f hf d
  have h := hJ d hf
  have hc : (DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) k) f d : Poly k N) =
      homogeneousComponent d f := decomposition.decompose'_apply f d
  rwa [hc] at h

/- English proof (translation)
Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, m, e, hf, hm, hfe, hme, rfl⟩`. Take `⟨g, hg, z, hz, hgz⟩` from `Submodule.mem_sup.mp hf`. Establish `hfe' : f = homogeneousComponent e g + homogeneousComponent e z`. Rewrite using `[← map_add, hgz, homogeneousComponent_eq_self hfe]`.

Rewrite using `[SetLike.mem_coe, hfe', map_add, add_div]`. Conclude with `Submodule.add_mem_sup (Submodule.subset_span ⟨_, m, e, hh g hg e, hm, homogeneousComponent_isHomogeneous _ _, hme, rfl⟩) (Submodule.subset_span ⟨_, m, e, hh' z hz e, hm, homogeneousComponent_isHomogeneous _ _, hme, rfl⟩)`.
-/
theorem idealMod_sup_le (pp pp' : Ideal (Poly k N)) (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp)
    (hh' : ∀ f ∈ pp', ∀ d : ℕ, homogeneousComponent d f ∈ pp') (I : Chart x) :
    idealMod (x := x) (pp ⊔ pp') I ≤ idealMod (x := x) pp I ⊔ idealMod (x := x) pp' I := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, m, e, hf, hm, hfe, hme, rfl⟩
  obtain ⟨g, hg, z, hz, hgz⟩ := Submodule.mem_sup.mp hf
  have hfe' : f = homogeneousComponent e g + homogeneousComponent e z := by
    rw [← map_add, hgz, homogeneousComponent_eq_self hfe]
  rw [SetLike.mem_coe, hfe', map_add, add_div]
  exact Submodule.add_mem_sup
    (Submodule.subset_span ⟨_, m, e, hh g hg e, hm, homogeneousComponent_isHomogeneous _ _, hme, rfl⟩)
    (Submodule.subset_span ⟨_, m, e, hh' z hz e, hm, homogeneousComponent_isHomogeneous _ _, hme, rfl⟩)

/- English proof (translation)
Establish `hge` using `one_le_ringKrullDim_of_relevant pp hh hrel`. Establish `hle : ringKrullDim (Poly k N ⧸ pp) ≤ ((N + 1 : ℕ) : WithBot ℕ∞)`. Use `(ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective).trans ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]`. Simplify using the standard rewrite rules.

Generalize the expression as in `ringKrullDim (Poly k N ⧸ pp) = d at hge hle`. Proceed by induction on `d using WithBot.recBotCoe with`. Consider the case `bot => exact absurd hge (by simp)`. Consider the case `coe d`. Proceed by induction on `d using ENat.recTopCoe with`.

Consider the case `top`. It suffices to derive a contradiction. Establish `h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((N + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)` using `hle`. Conclude with `ENat.natCast_ne_top (N + 1) (top_le_iff.mp (WithBot.coe_le_coe.mp h2))`. Consider the case `coe m`.

Establish `h1 : 1 ≤ m` using `by exact_mod_cast hge`. Conclude with `⟨m - 1, by rw [Nat.sub_add_cancel h1]; rfl⟩`.
-/
theorem exists_dim_eq (pp : Ideal (Poly k N)) [pp.IsPrime] (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp)
    (hrel : ∃ i, (X i : Poly k N) ∉ pp) :
    ∃ e : ℕ, ringKrullDim (Poly k N ⧸ pp) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
  have hge := one_le_ringKrullDim_of_relevant pp hh hrel
  have hle : ringKrullDim (Poly k N ⧸ pp) ≤ ((N + 1 : ℕ) : WithBot ℕ∞) := by
    refine (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  generalize ringKrullDim (Poly k N ⧸ pp) = d at hge hle
  induction d using WithBot.recBotCoe with
  | bot => exact absurd hge (by simp)
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((N + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := hle
      exact ENat.natCast_ne_top (N + 1) (top_le_iff.mp (WithBot.coe_le_coe.mp h2))
    | coe m =>
      have h1 : 1 ≤ m := by exact_mod_cast hge
      exact ⟨m - 1, by rw [Nat.sub_add_cancel h1]; rfl⟩

end SnapperSections

open SnapperSections in

/- English proof (translation)
Introduce `k _ Ω _ _ N x pp hp hh hle hrel t L j a`. Use `hp` as an intermediate fact. Take `⟨μ, hμ⟩` from `Generated.full k Ω N x (L j)`. Take `⟨D, hDdef⟩ : ∃ D : LineBundle k x, D = (L j).tensorProd (twistBundle k x μ)` from `⟨_, rfl⟩`. Establish `hDgen : D.toSubSystem.Generated` using `hDdef ▸ hμ μ le_rfl`.

Establish `hDsub : ∀ I, D.sub I = (twistSys k x μ).sub I * (L j).sub I` using `fun I => by`. Rewrite using `[hDdef, tensorProd_sub (L j) (twistBundle k x μ) I, twistBundle_sub]`. Take `⟨s, hs, I₀, hsI₀⟩` from `hN k Ω N x pp hp hh hle hrel D hDgen`. Establish `hs0 : s ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hsI₀ (Submodule.zero_mem _)`. Establish `hsD : ∀ I, s ∈ D.sub I` using `fun I => (Submodule.mem_iInf _).mp hs I`. Take `⟨e, he⟩` from `exists_dim_eq pp hh hrel`. Take `⟨f₀, hf₀Z, hf₀p⟩` from `CutZeroNotLe.proof k Ω N x e pp D s ⟨hp, hh, hle, hrel, he⟩ hs ⟨I₀, hsI₀⟩`. Take `⟨Zs, hZs⟩ : ∃ Zs : Ideal (Poly k N), Zs = zeroIdeal D.toSubSystem s` from `⟨_, rfl⟩`.

Establish `hZh : ∀ f ∈ Zs, ∀ d : ℕ, homogeneousComponent d f ∈ Zs` using `hZs ▸ zeroIdeal_homog _ s`. Establish `hJh : ∀ f ∈ pp ⊔ Zs, ∀ d : ℕ, homogeneousComponent d f ∈ pp ⊔ Zs`. Introduce `f hf d`. Take `⟨g, hg, z, hz, rfl⟩` from `Submodule.mem_sup.mp hf`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem_sup (hh g hg d) (hZh z hz d)`. Take `⟨F₁, hF₁def⟩ : ∃ F₁ : LineBundle k x, F₁ = (twistBundle k x a).tensorProd D` from `⟨_, rfl⟩`. Establish `hF₁sub : ∀ I, F₁.sub I = D.sub I * (twistSys k x a).sub I` using `fun I => by`. Rewrite using `[hF₁def, tensorProd_sub (twistBundle k x a) D I, twistBundle_sub]`. Take `⟨G₀, hG₀, -⟩` from `IdealTwistFamily.proof k Ω N x F₁ pp hh`.

Establish `hG₀sub : ∀ I, G₀.sub I = idealMod (x` using `x) pp I * (D.sub I * (twistSys k x a).sub I) := fun I => by`. Rewrite using `[hG₀, SubSystem.twist_sub_eq_mul_of_line, idealSys_sub]`. Rewrite using `[hF₁sub]`. Take `⟨F₂, hF₂def⟩ : ∃ F₂ : SubFamily k x Ω, F₂ = SubFamily.sup ((twistBundle k x a).tensorProd (spanBundle k x s hs0)).toSubFamily G₀` from `⟨_, rfl⟩`. Establish `hF₂sub : ∀ I, F₂.sub I = Submodule.span (chartRing k x I) {s} * (twistSys k x a).sub I ⊔ idealMod (x` using `x) pp I * (D.sub I * (twistSys k x a).sub I) := fun I => by`.

Rewrite using `[hF₂def, supFam_sub, tensorProd_sub (twistBundle k x a) (spanBundle k x s hs0) I, spanBundle_sub, twistBundle_sub, hG₀sub]`. Establish `hF₂₁ : ∀ I, F₂.sub I ≤ F₁.sub I` using `fun I => by`. Rewrite using `[hF₂sub, hF₁sub]`. Use `sup_le (mul_le_mul_sub ((Submodule.span_singleton_le_iff_mem _ _).mpr (hsD I)) le_rfl) ?_` and prove the remaining obligations. Conclude with `(mul_le_mul_sub (idealMod_le_one pp I) le_rfl).trans_eq (one_mul _)`.

Establish `hJF : ∀ I, (F₁.toSubFamily.toSubSystem.twist (idealSys x (pp ⊔ Zs))).sub I ≤ F₂.sub I` using `fun I => by`. Rewrite using `[SubSystem.twist_sub_eq_mul_of_line, idealSys_sub, hF₂sub]`. Express the relevant statement in the definitionally equal form `idealMod (x := x) (pp ⊔ Zs) I * F₁.sub I ≤ _`. Rewrite using `[hF₁sub]`. Use `(mul_le_mul_sub (idealMod_sup_le pp Zs hh hZh I) le_rfl).trans ?_` and prove the remaining obligations.

Rewrite using `[Submodule.sup_mul]`. Use `sup_le le_sup_right (le_sup_of_le_left ?_)` and prove the remaining obligations. Rewrite using `[← mul_assoc, hZs]`. Conclude with `mul_le_mul_sub (StepThree.Away.idealMod_zeroIdeal_mul_le D.toSubSystem s I) le_rfl`. Take `⟨r, qq, b, hqq, hdev⟩` from `hD k Ω N x Ω F₁.toSubFamily F₂ F₁.fg hF₂₁ (pp ⊔ Zs) hJh (hle.trans le_sup_left) hJF`.

Use `⟨μ, r, qq, b, fun m => ⟨(hqq m).1, (hqq m).2.1, lt_of_le_of_ne (le_sup_left.trans (hqq m).2.2) fun h => hf₀p ?_⟩, fun n c => ?_⟩` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `(hqq m).2.2 (Ideal.mem_sup_right (hZs ▸ hf₀Z))`. Take `⟨M, hMdef⟩ : ∃ M : LineBundle k x, M = (powsBundle (twistBundle k x a) t L n).tensorProd (twistBundle k x c)` from `⟨_, rfl⟩`. Establish `hMsub : ∀ I, M.sub I = (twistSys k x c).sub I * ((twistSys k x a).sub I * ∏ i, (L i).sub I ^ n i)` using `fun I => by`.

Rewrite using `[hMdef, tensorProd_sub (powsBundle (twistBundle k x a) t L n) (twistBundle k x c) I, powsBundle_sub, twistBundle_sub, twistBundle_sub]`. Establish `hMD : ∀ I, (M.tensorProd D).sub I = D.sub I * M.sub I` using `fun I => tensorProd_sub M D I`. Take `⟨G₁, hG₁, -⟩` from `IdealTwistFamily.proof k Ω N x (M.tensorProd D) pp hh`. Establish `hG₁sub : ∀ I, G₁.sub I = idealMod (x` using `x) pp I * (D.sub I * M.sub I) := fun I => by`. Rewrite using `[hG₁, SubSystem.twist_sub_eq_mul_of_line, idealSys_sub, hMD]`.

Take `⟨F₂', hF₂'def⟩ : ∃ F₂' : SubFamily k x Ω, F₂' = SubFamily.sup (M.tensorProd (spanBundle k x s hs0)).toSubFamily G₁` from `⟨_, rfl⟩`. Establish `hF₂'sub : ∀ I, F₂'.sub I = Submodule.span (chartRing k x I) {s} * M.sub I ⊔ idealMod (x` using `x) pp I * (D.sub I * M.sub I) := fun I => by`. Rewrite using `[hF₂'def, supFam_sub, tensorProd_sub M (spanBundle k x s hs0) I, spanBundle_sub, hG₁sub]`. Establish `hadd` using `hA k Ω N x Ω (M.tensorProd D).toSubFamily F₂' G₁ (M.tensorProd D).fg (fun I => by`. Rewrite using `[hF₂'sub, hMD]`.

Use `sup_le (mul_le_mul_sub ((Submodule.span_singleton_le_iff_mem _ _).mpr (hsD I)) le_rfl) ?_` and prove the remaining obligations. Conclude with `(mul_le_mul_sub (idealMod_le_one pp I) le_rfl).trans_eq (one_mul _))`. Use the proof step `(fun I => by rw [hF₂'sub, hG₁sub]; exact le_sup_right)`. Establish `hmul` using `hM k Ω N x M.toSubSystem (M.toSubSystem.twist (idealSys x pp)) F₂'.toSubSystem G₁.toSubSystem s (fun I y hy => by`. Rewrite using `[hF₂'sub]`.

Conclude with `Submodule.mem_sup_left (Submodule.mul_mem_mul (Submodule.mem_span_singleton_self s) hy))`. Use the proof step `(fun I z hz => by`. Express the relevant statement in the definitionally equal form `z ∈ F₂'.sub I at hz`. Rewrite `hz` using `[hF₂'sub]`. Take `⟨z₁, hz₁, z₂, hz₂, rfl⟩` from `Submodule.mem_sup.mp hz`.

Take `⟨y, hy, rfl⟩` from `Submodule.mem_span_singleton_mul.mp hz₁`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[hG₁sub, add_sub_cancel_left]`. Conclude with `hz₂)`. Use the proof step `(fun I y hy => by`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `hI k Ω N x pp hp hh hle D M s ⟨f₀, hf₀Z, hf₀p⟩ I y hy ?_` and prove the remaining obligations. Rewrite `h` using `[hG₁]`. Conclude with `h`.

Introduce `h`. Rewrite `h` using `[SubSystem.twist_sub_eq_mul_of_line, idealSys_sub]`. Rewrite using `[hG₁sub, show idealMod (x := x) pp I * (D.sub I * M.sub I) = idealMod (x := x) pp I * M.sub I * D.sub I by ring, mul_comm s y]`. Conclude with `Submodule.mul_mem_mul h (hsD I))`. Establish `hE1 : pieceChar k pp a L (Function.update n j (n j + 1)) (c + μ) = eulerCharQuot k (M.tensorProd D).toSubSystem G₁.toSubSystem`.

Unfold `pieceChar`. Apply the tactic sequence `congr 1 <;> refine SubSystem.ext_sub fun I => ?_`. Rewrite using `[SubSystem.twist_sub_eq_mul_of_line, twistPows_sub, prod_update_pow, ← twistSys_sub_mul]`. Rewrite using `[hMD, hMsub, hDsub]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[SubSystem.twist_sub_eq_mul_of_line, twistPows_sub, prod_update_pow, ← twistSys_sub_mul, SubSystem.twist_sub_eq_mul_of_line, idealSys_sub]`. Rewrite using `[hG₁sub, hMsub, hDsub]`. Expand and normalize the polynomial expressions, which then agree. Establish `hE2 : pieceChar k pp a L n c = eulerCharQuot k M.toSubSystem (M.toSubSystem.twist (idealSys x pp))`. Unfold `pieceChar`.

Apply the tactic sequence `congr 1 <;> refine SubSystem.ext_sub fun I => ?_`. Rewrite using `[SubSystem.twist_sub_eq_mul_of_line, twistPows_sub]`. Rewrite using `[hMsub]`. Rewrite using `[SubSystem.twist_sub_eq_mul_of_line, twistPows_sub, SubSystem.twist_sub_eq_mul_of_line, idealSys_sub, SubSystem.twist_sub_eq_mul_of_line, idealSys_sub]`. Rewrite using `[hMsub]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hE3 : eulerCharQuot k ((F₁.toSubFamily.toSubSystem.twistPows t (fun i => (L i).toSubSystem) n).twist (twistSys k x c)) ((F₂.toSubSystem.twistPows t (fun i => (L i).toSubSystem) n).twist (twistSys k x c)) = eulerCharQuot k (M.tensorProd D).toSubSystem F₂'.toSubSystem`. Apply the tactic sequence `congr 1 <;> refine SubSystem.ext_sub fun I => ?_`. Rewrite using `[SubSystem.twist_sub_eq_mul_of_line, twistPows_sub]`. Rewrite using `[hF₁sub, hMD, hMsub]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[SubSystem.twist_sub_eq_mul_of_line, twistPows_sub]`. Rewrite using `[hF₂sub, hF₂'sub, hMsub]`. Simplify using `only [← Submodule.add_eq_sup]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hE1, hE2, hadd, hmul, ← hE3, hdev t L n c]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem SnapperSection.proof (hA : SnapperQuotAdd.Statement.{u, w, w})
    (hD : SnapperQuotDevissage.Statement.{u, w, w}) (hM : MulQuotEq.Statement.{u, w})
    (hN : SectionNonvanish.Statement.{u, w}) (hI : SectionMulInj.Statement.{u, w}) :
    SnapperSection.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hp hh hle hrel t L j a
  have := hp

  obtain ⟨μ, hμ⟩ := Generated.full k Ω N x (L j)
  obtain ⟨D, hDdef⟩ : ∃ D : LineBundle k x, D = (L j).tensorProd (twistBundle k x μ) := ⟨_, rfl⟩
  have hDgen : D.toSubSystem.Generated := hDdef ▸ hμ μ le_rfl
  have hDsub : ∀ I, D.sub I = (twistSys k x μ).sub I * (L j).sub I := fun I => by
    rw [hDdef, tensorProd_sub (L j) (twistBundle k x μ) I, twistBundle_sub]
  obtain ⟨s, hs, I₀, hsI₀⟩ := hN k Ω N x pp hp hh hle hrel D hDgen
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hsI₀ (Submodule.zero_mem _)
  have hsD : ∀ I, s ∈ D.sub I := fun I => (Submodule.mem_iInf _).mp hs I
  obtain ⟨e, he⟩ := exists_dim_eq pp hh hrel
  obtain ⟨f₀, hf₀Z, hf₀p⟩ := CutZeroNotLe.proof k Ω N x e pp D s ⟨hp, hh, hle, hrel, he⟩ hs ⟨I₀, hsI₀⟩

  obtain ⟨Zs, hZs⟩ : ∃ Zs : Ideal (Poly k N), Zs = zeroIdeal D.toSubSystem s := ⟨_, rfl⟩
  have hZh : ∀ f ∈ Zs, ∀ d : ℕ, homogeneousComponent d f ∈ Zs := hZs ▸ zeroIdeal_homog _ s
  have hJh : ∀ f ∈ pp ⊔ Zs, ∀ d : ℕ, homogeneousComponent d f ∈ pp ⊔ Zs := by
    intro f hf d
    obtain ⟨g, hg, z, hz, rfl⟩ := Submodule.mem_sup.mp hf
    rw [map_add]
    exact Submodule.add_mem_sup (hh g hg d) (hZh z hz d)
  obtain ⟨F₁, hF₁def⟩ : ∃ F₁ : LineBundle k x, F₁ = (twistBundle k x a).tensorProd D := ⟨_, rfl⟩
  have hF₁sub : ∀ I, F₁.sub I = D.sub I * (twistSys k x a).sub I := fun I => by
    rw [hF₁def, tensorProd_sub (twistBundle k x a) D I, twistBundle_sub]
  obtain ⟨G₀, hG₀, -⟩ := IdealTwistFamily.proof k Ω N x F₁ pp hh
  have hG₀sub : ∀ I, G₀.sub I = idealMod (x := x) pp I * (D.sub I * (twistSys k x a).sub I) := fun I => by
    rw [hG₀, SubSystem.twist_sub_eq_mul_of_line, idealSys_sub]
    rw [hF₁sub]
  obtain ⟨F₂, hF₂def⟩ : ∃ F₂ : SubFamily k x Ω,
      F₂ = SubFamily.sup ((twistBundle k x a).tensorProd (spanBundle k x s hs0)).toSubFamily G₀ := ⟨_, rfl⟩
  have hF₂sub : ∀ I, F₂.sub I = Submodule.span (chartRing k x I) {s} * (twistSys k x a).sub I ⊔
      idealMod (x := x) pp I * (D.sub I * (twistSys k x a).sub I) := fun I => by
    rw [hF₂def, supFam_sub, tensorProd_sub (twistBundle k x a) (spanBundle k x s hs0) I, spanBundle_sub,
      twistBundle_sub, hG₀sub]
  have hF₂₁ : ∀ I, F₂.sub I ≤ F₁.sub I := fun I => by
    rw [hF₂sub, hF₁sub]
    refine sup_le (mul_le_mul_sub ((Submodule.span_singleton_le_iff_mem _ _).mpr (hsD I)) le_rfl) ?_
    exact (mul_le_mul_sub (idealMod_le_one pp I) le_rfl).trans_eq (one_mul _)
  have hJF : ∀ I, (F₁.toSubFamily.toSubSystem.twist (idealSys x (pp ⊔ Zs))).sub I ≤ F₂.sub I := fun I => by
    rw [SubSystem.twist_sub_eq_mul_of_line, idealSys_sub, hF₂sub]
    change idealMod (x := x) (pp ⊔ Zs) I * F₁.sub I ≤ _
    rw [hF₁sub]
    refine (mul_le_mul_sub (idealMod_sup_le pp Zs hh hZh I) le_rfl).trans ?_
    rw [Submodule.sup_mul]
    refine sup_le le_sup_right (le_sup_of_le_left ?_)
    rw [← mul_assoc, hZs]
    exact mul_le_mul_sub (StepThree.Away.idealMod_zeroIdeal_mul_le D.toSubSystem s I) le_rfl
  obtain ⟨r, qq, b, hqq, hdev⟩ := hD k Ω N x Ω F₁.toSubFamily F₂ F₁.fg hF₂₁ (pp ⊔ Zs) hJh
    (hle.trans le_sup_left) hJF
  refine ⟨μ, r, qq, b, fun m => ⟨(hqq m).1, (hqq m).2.1, lt_of_le_of_ne (le_sup_left.trans (hqq m).2.2)
    fun h => hf₀p ?_⟩, fun n c => ?_⟩
  · rw [h]
    exact (hqq m).2.2 (Ideal.mem_sup_right (hZs ▸ hf₀Z))

  obtain ⟨M, hMdef⟩ : ∃ M : LineBundle k x,
      M = (powsBundle (twistBundle k x a) t L n).tensorProd (twistBundle k x c) := ⟨_, rfl⟩
  have hMsub : ∀ I, M.sub I = (twistSys k x c).sub I * ((twistSys k x a).sub I * ∏ i, (L i).sub I ^ n i) :=
    fun I => by
      rw [hMdef, tensorProd_sub (powsBundle (twistBundle k x a) t L n) (twistBundle k x c) I, powsBundle_sub,
        twistBundle_sub, twistBundle_sub]
  have hMD : ∀ I, (M.tensorProd D).sub I = D.sub I * M.sub I := fun I => tensorProd_sub M D I
  obtain ⟨G₁, hG₁, -⟩ := IdealTwistFamily.proof k Ω N x (M.tensorProd D) pp hh
  have hG₁sub : ∀ I, G₁.sub I = idealMod (x := x) pp I * (D.sub I * M.sub I) := fun I => by
    rw [hG₁, SubSystem.twist_sub_eq_mul_of_line, idealSys_sub, hMD]
  obtain ⟨F₂', hF₂'def⟩ : ∃ F₂' : SubFamily k x Ω,
      F₂' = SubFamily.sup (M.tensorProd (spanBundle k x s hs0)).toSubFamily G₁ := ⟨_, rfl⟩
  have hF₂'sub : ∀ I, F₂'.sub I = Submodule.span (chartRing k x I) {s} * M.sub I ⊔
      idealMod (x := x) pp I * (D.sub I * M.sub I) := fun I => by
    rw [hF₂'def, supFam_sub, tensorProd_sub M (spanBundle k x s hs0) I, spanBundle_sub, hG₁sub]

  have hadd := hA k Ω N x Ω (M.tensorProd D).toSubFamily F₂' G₁ (M.tensorProd D).fg
    (fun I => by
      rw [hF₂'sub, hMD]
      refine sup_le (mul_le_mul_sub ((Submodule.span_singleton_le_iff_mem _ _).mpr (hsD I)) le_rfl) ?_
      exact (mul_le_mul_sub (idealMod_le_one pp I) le_rfl).trans_eq (one_mul _))
    (fun I => by rw [hF₂'sub, hG₁sub]; exact le_sup_right)

  have hmul := hM k Ω N x M.toSubSystem (M.toSubSystem.twist (idealSys x pp)) F₂'.toSubSystem G₁.toSubSystem s
    (fun I y hy => by
      rw [hF₂'sub]
      exact Submodule.mem_sup_left (Submodule.mul_mem_mul (Submodule.mem_span_singleton_self s) hy))
    (fun I z hz => by
      change z ∈ F₂'.sub I at hz
      rw [hF₂'sub] at hz
      obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_span_singleton_mul.mp hz₁
      refine ⟨y, hy, ?_⟩
      rw [hG₁sub, add_sub_cancel_left]
      exact hz₂)
    (fun I y hy => by
      constructor
      · intro h
        refine hI k Ω N x pp hp hh hle D M s ⟨f₀, hf₀Z, hf₀p⟩ I y hy ?_
        rw [hG₁] at h
        exact h
      · intro h
        rw [SubSystem.twist_sub_eq_mul_of_line, idealSys_sub] at h
        rw [hG₁sub, show idealMod (x := x) pp I * (D.sub I * M.sub I) =
          idealMod (x := x) pp I * M.sub I * D.sub I by ring, mul_comm s y]
        exact Submodule.mul_mem_mul h (hsD I))

  have hE1 : pieceChar k pp a L (Function.update n j (n j + 1)) (c + μ) =
      eulerCharQuot k (M.tensorProd D).toSubSystem G₁.toSubSystem := by
    unfold pieceChar
    congr 1 <;> refine SubSystem.ext_sub fun I => ?_
    · rw [SubSystem.twist_sub_eq_mul_of_line, twistPows_sub, prod_update_pow, ← twistSys_sub_mul]
      rw [hMD, hMsub, hDsub]
      ring
    · rw [SubSystem.twist_sub_eq_mul_of_line, twistPows_sub, prod_update_pow, ← twistSys_sub_mul,
        SubSystem.twist_sub_eq_mul_of_line, idealSys_sub]
      rw [hG₁sub, hMsub, hDsub]
      ring
  have hE2 : pieceChar k pp a L n c = eulerCharQuot k M.toSubSystem (M.toSubSystem.twist (idealSys x pp)) := by
    unfold pieceChar
    congr 1 <;> refine SubSystem.ext_sub fun I => ?_
    · rw [SubSystem.twist_sub_eq_mul_of_line, twistPows_sub]
      rw [hMsub]
    · rw [SubSystem.twist_sub_eq_mul_of_line, twistPows_sub, SubSystem.twist_sub_eq_mul_of_line, idealSys_sub,
        SubSystem.twist_sub_eq_mul_of_line, idealSys_sub]
      rw [hMsub]
      ring
  have hE3 : eulerCharQuot k
      ((F₁.toSubFamily.toSubSystem.twistPows t (fun i => (L i).toSubSystem) n).twist (twistSys k x c))
      ((F₂.toSubSystem.twistPows t (fun i => (L i).toSubSystem) n).twist (twistSys k x c)) =
      eulerCharQuot k (M.tensorProd D).toSubSystem F₂'.toSubSystem := by
    congr 1 <;> refine SubSystem.ext_sub fun I => ?_
    · rw [SubSystem.twist_sub_eq_mul_of_line, twistPows_sub]
      rw [hF₁sub, hMD, hMsub]
      ring
    · rw [SubSystem.twist_sub_eq_mul_of_line, twistPows_sub]
      rw [hF₂sub, hF₂'sub, hMsub]
      simp only [← Submodule.add_eq_sup]
      ring
  rw [hE1, hE2, hadd, hmul, ← hE3, hdev t L n c]
  ring

end

end GroundTheory.Heights₂.Heights.Kleiman
