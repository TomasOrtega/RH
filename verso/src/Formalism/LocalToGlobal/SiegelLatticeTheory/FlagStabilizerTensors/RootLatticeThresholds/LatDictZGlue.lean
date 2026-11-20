import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZGlueA

noncomputable section

open NumberField Matrix IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.LatDictZ.Z5

open Formalism.MainNotions.S PIW.AdelClassFin Formalism.L2.SG.Pf.LatDictZ

/- English proof (translation)
Introduce `I r s z M hMfg hMsp hfin γ hγU hγs hγz hloc`. Set `Q : Set (HeightOneSpectrum (𝓞 I.F))` to `{q | ∃ p : Ideal (𝓞 I.E), p.IsMaximal ∧ locE I p M ≠ locE I p I.L ∧ p.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = q.asIdeal}`. Establish `hQ : Q.Finite`. Use `DictRing.nonempty_places (F := I.F)` as an intermediate fact. Use `(hfin.image fun p => if hp : p.IsMaximal then under I p hp else Classical.arbitrary _).subset ?_` and prove the remaining obligations.

Introduce and unpack `q ⟨p, hp, hne, hq⟩`. Use `⟨p, ⟨hp, hne⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [dif_pos hp]`. Conclude with `HeightOneSpectrum.ext hq`. Establish `hQex : ∀ q ∈ Q, ∃ p : Ideal (𝓞 I.E), p.IsMaximal ∧ p.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = q.asIdeal` using `fun q ⟨p, hp, _, hq⟩ => ⟨p, hp, hq⟩`.

Set `g : HeightOneSpectrum (𝓞 I.F) → GL (Fin I.n) I.E` to `fun q => if h : q ∈ Q then γ (Classical.choose (hQex q h)) else 1`. Establish `hgU : ∀ q, g q ∈ Formalism.UG.UJ (starRingEnd I.E) I.J` using `fun q => by`. Distinguish the cases in `h : q ∈ Q`. Simplify using `only [g, dif_pos h]`. Conclude with `hγU _`.

Simplify using `only [g, dif_neg h]`. Conclude with `one_mem _`. Establish `hgs : ∀ q a, (g q : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ s a = s a` using `fun q a => by`. Distinguish the cases in `h : q ∈ Q`. Simplify using `only [g, dif_pos h]`.

Conclude with `hγs _ a`. Simplify using `only [g, dif_neg h, Units.val_one, Matrix.one_mulVec]`. Establish `hgz : ∀ q, (g q : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z = z` using `fun q => by`. Distinguish the cases in `h : q ∈ Q`. Simplify using `only [g, dif_pos h]`.

Conclude with `hγz _`. Simplify using `only [g, dif_neg h, Units.val_one, Matrix.one_mulVec]`. Establish `hgloc : ∀ q ∈ Q, ∀ p : Ideal (𝓞 I.E), p.IsMaximal → p.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = q.asIdeal → ∀ v, v ∈ locE I p M ↔ ∃ w ∈ locE I p I.L, (g q : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ w = v`. Introduce `q hq p hp hpq v`. Establish `hc` using `Classical.choose_spec (hQex q hq)`.

Simplify using `only [g, dif_pos hq]`. Rewrite using `[loc_congr I hp hc.1 (hpq.trans hc.2.symm) M, loc_congr I hp hc.1 (hpq.trans hc.2.symm) I.L]`. Conclude with `hloc _ hc.1 v`. Set `Qs` to `hQ.toFinset`. Set `ε : HeightOneSpectrum (𝓞 I.F) → I.E ⊗[I.F] Af I.F` to `fun q => iA I (eT {q})`.

Set `φ : I.E ⊗[I.F] Af I.F` to `iA I (eT Qᶜ)`. Establish `horth : Orth Qs ε` using `fun i _ j _ => by`. Simplify using `only [ε]`. Rewrite using `[← map_mul, eT_orth]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hφε : ∀ i ∈ Qs, φ * ε i = 0` using `fun i hi => by`. Simplify using `only [φ, ε]`. Rewrite using `[← map_mul, eT_compl_mul (hQ.mem_toFinset.1 hi), map_zero]`. Establish `hsum : φ + ∑ i ∈ Qs, ε i = 1`. Simplify using `only [φ, ε]`.

Rewrite using `[← map_sum, ← map_add, eT_sum hQ, map_one]`. Set `G : HeightOneSpectrum (𝓞 I.F) → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)` to `fun q => (g q : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))`. Set `Gi : HeightOneSpectrum (𝓞 I.F) → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)` to `fun q => (((g q)⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))`. Establish `hGGi : ∀ q, G q * Gi q = 1` using `fun q => by`. Simplify using `only [G, Gi]`.

Rewrite using `[← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hGiG : ∀ q, Gi q * G q = 1` using `fun q => by`. Simplify using `only [G, Gi]`. Rewrite using `[← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hXY : gl Qs ε 1 G * gl Qs ε 1 Gi = 1`.

Rewrite using `[gl_mul horth]`. Simplify using `only [hGGi, mul_one]`. Conclude with `gl_const _ _ _`. Establish `hYX : gl Qs ε 1 Gi * gl Qs ε 1 G = 1`. Rewrite using `[gl_mul horth]`.

Simplify using `only [hGiG, mul_one]`. Conclude with `gl_const _ _ _`. Set `σR` to `Formalism.UG.sigR I.cm.sig (Af I.F)`. Set `J'` to `I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))`. Establish `hσε : ∀ i ∈ Qs, σR (ε i) = ε i` using `fun i _ => by`.

Simplify using `only [σR, ε]`. Rewrite using `[Algebra.TensorProduct.includeRight_apply]`. Conclude with `DictLat.sigR_one_tmul I _`. Establish `hcG : ∀ q, Formalism.UG.cT σR (G q) = (Formalism.UG.cT (starRingEnd I.E) (g q : Matrix (Fin I.n) (Fin I.n) I.E)).map (Formalism.UG.inclE (F` using `I.F) (Af I.F)) := fun q => by`. Use extensionality with `a b`.

Simplify using `only [Formalism.UG.cT, G, σR, Matrix.map_apply, Matrix.transpose_apply, DictLat.sigR_inclE, starRingEnd_apply]`. Establish `hGu : ∀ q, Formalism.UG.cT σR (G q) * J' * G q = J'` using `fun q => by`. Rewrite using `[hcG]`. Simplify using `only [G, J']`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul]`.

Conclude with `congrArg (fun N => N.map (Formalism.UG.inclE (F := I.F) (Af I.F))) (show Formalism.UG.cT (starRingEnd I.E) (g q : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * (g q : Matrix (Fin I.n) (Fin I.n) I.E) = I.J from hgU q)`. Establish `hXU : Formalism.UG.cT σR (gl Qs ε 1 G) * J' * gl Qs ε 1 G = J'`. Rewrite using `[cT_gl σR hσε, Formalism.UG.cT_one]`. Use `conv_lhs => rw [show J' = gl Qs ε J' (fun _ => J') from (gl_const _ _ _).symm]`. Rewrite using `[gl_mul horth, gl_mul horth]`.

Simplify using `only [hGu, mul_one, one_mul]`. Conclude with `gl_const _ _ _`. Set `xg : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)` to `⟨gl Qs ε 1 G, gl Qs ε 1 Gi, hXY, hYX⟩`. Establish `hxU : xg ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F)` using `hXU`. Set `x : I.Gf` to `⟨xg, hxU⟩`.

Establish `hfx : I.fmat x = gl Qs ε 1 G` using `rfl`. Establish `hfxi : I.fmat x⁻¹ = gl Qs ε 1 Gi` using `rfl`. Establish `hfix : ∀ u : Fin I.n → I.E, (∀ q, (g q : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u = u) → I.fmat x *ᵥ iv I u = iv I u`. Introduce `u hu`. Rewrite using `[hfx, gl_mulVec, Matrix.one_mulVec, Finset.sum_eq_zero (fun q _ => ?_), add_zero]`.

Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Simplify using `only [G]`. Rewrite using `[dictTop_map_mulVec, hu, sub_self, smul_zero]`. Use `⟨x, fun a => hfix _ (fun q => hgs q a), hfix _ hgz, ?_⟩` and prove the remaining obligations. Use extensionality with `v`.

Use `show I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf ↔ v ∈ M`. Rewrite using `[hfxi]`. Establish `hdec : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, y ∈ I.Lf ↔ φ • y ∈ I.Lf ∧ ∀ q ∈ Qs, ε q • y ∈ I.Lf`. Introduce `y`. Use `⟨fun h => ⟨DictLat.Lf_smul I (iA_mem I (eT_mem _)) h, fun q _ => DictLat.Lf_smul I (iA_mem I (eT_mem _)) h⟩, fun ⟨h0, h1⟩ => ?_⟩` and prove the remaining obligations.

Establish `hy : y = φ • y + ∑ q ∈ Qs, ε q • y`. Rewrite using `[← Finset.sum_smul, ← add_smul, hsum, one_smul]`. Rewrite using `[hy]`. Conclude with `add_mem h0 (Submodule.sum_mem _ h1)`. Establish `hproj : ∀ q ∈ Qs, ε q • (gl Qs ε 1 Gi *ᵥ iv I v) = ε q • iv I ((((g q)⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ v)` using `fun q hq => by`.

Rewrite using `[gl_proj horth _ _ _ hq]`. Simplify using `only [Gi]`. Rewrite using `[dictTop_map_mulVec]`. Establish `hproj0 : φ • (gl Qs ε 1 Gi *ᵥ iv I v) = φ • iv I v`. Rewrite using `[gl_proj0 hφε, Matrix.one_mulVec]`.

Rewrite using `[hdec, hproj0]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, h1⟩`. Use `Formalism.HermitianLatticesTheory.locBasic_lg (fun p => Formalism.HermitianLatticesTheory.hcompl (K := I.E) p) (fun p hp s hs => by have := hp.isPrime; exact Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem (K := I.E) p s hs) M v (fun p hp => ?_)` and prove the remaining obligations. Use `show v ∈ locE I p M`.

Distinguish the cases in `hq : under I p hp ∈ Q`. Establish `h2` using `h1 _ (hQ.mem_toFinset.2 hq)`. Rewrite `h2` using `[hproj _ (hQ.mem_toFinset.2 hq)]`. Take `⟨a, ha, haw⟩` from `descent I (under I p hp) (eT_mem _) (eT_of_mem (Set.mem_singleton _)) _ h2`. Rewrite using `[hgloc _ hq p hp rfl]`.

Conclude with `⟨_, (loc_iff I p hp _ _).2 ⟨a, ha, haw⟩, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩`. Take `⟨a, ha, haw⟩` from `descent I (under I p hp) (eT_mem _) (eT_of_mem hq) _ h0`. Establish `hne : locE I p M = locE I p I.L`. Assume the negation of the conclusion as `hne`. Conclude with `hq ⟨p, hp, hne, rfl⟩`.

Rewrite using `[hne]`. Conclude with `(loc_iff I p hp _ _).2 ⟨a, ha, haw⟩`. Introduce `hv`. Use `⟨?_, fun q hq => ?_⟩` and prove the remaining obligations. Apply `glue I Qᶜ v` to reduce the goal to its premises.

Introduce `q hq`. Establish `hker : RingHom.ker (algebraMap (𝓞 I.F) (𝓞 I.E)) ≤ q.asIdeal`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 (alg_inj I)]`. Conclude with `bot_le`. Take `⟨p, hp, hpq⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 I.E) q.asIdeal hker`.

Establish `hne : locE I p M = locE I p I.L`. Assume the negation of the conclusion as `hne`. Conclude with `hq ⟨p, hp, hne, hpq⟩`. Establish `h3 : v ∈ locE I p M` using `Formalism.HermitianLatticesTheory.locBasic_le_locS _ M hv`. Rewrite `h3` using `[hne]`.

Take `⟨a, ha, haw⟩` from `(loc_iff I p hp _ _).1 h3`. Conclude with `⟨a, hpq ▸ ha, haw⟩`. Rewrite using `[hproj q hq]`. Apply `glue I {q} _` to reduce the goal to its premises. Introduce `q' hq'`.

Rewrite `hq'` using `[Set.mem_singleton_iff]`. Substitute `hq'` using the available equality. Establish `hqQ` using `hQ.mem_toFinset.1 hq`. Take `⟨p, hp, hpq⟩` from `hQex q' hqQ`. Take `⟨w, hw, hgw⟩` from `(hgloc q' hqQ p hp hpq v).1 (Formalism.HermitianLatticesTheory.locBasic_le_locS _ M hv)`.

Establish `hw' : w = (((g q')⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ v`. Rewrite using `[← hgw, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Take `⟨a, ha, haw⟩` from `(loc_iff I p hp _ _).1 hw`. Conclude with `⟨a, hpq ▸ ha, hw' ▸ haw⟩`.
-/
theorem adelic_gluing : Z0.AdelGlue := by
  intro I r s z M hMfg hMsp hfin γ hγU hγs hγz hloc
  classical

  let Q : Set (HeightOneSpectrum (𝓞 I.F)) := {q | ∃ p : Ideal (𝓞 I.E), p.IsMaximal ∧
    locE I p M ≠ locE I p I.L ∧ p.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = q.asIdeal}
  have hQ : Q.Finite := by
    have := DictRing.nonempty_places (F := I.F)
    refine (hfin.image fun p => if hp : p.IsMaximal then under I p hp else Classical.arbitrary _).subset ?_
    rintro q ⟨p, hp, hne, hq⟩
    refine ⟨p, ⟨hp, hne⟩, ?_⟩
    simp only [dif_pos hp]
    exact HeightOneSpectrum.ext hq
  have hQex : ∀ q ∈ Q, ∃ p : Ideal (𝓞 I.E), p.IsMaximal ∧
      p.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = q.asIdeal :=
    fun q ⟨p, hp, _, hq⟩ => ⟨p, hp, hq⟩

  let g : HeightOneSpectrum (𝓞 I.F) → GL (Fin I.n) I.E := fun q =>
    if h : q ∈ Q then γ (Classical.choose (hQex q h)) else 1
  have hgU : ∀ q, g q ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := fun q => by
    by_cases h : q ∈ Q
    · simp only [g, dif_pos h]; exact hγU _
    · simp only [g, dif_neg h]; exact one_mem _
  have hgs : ∀ q a, (g q : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ s a = s a := fun q a => by
    by_cases h : q ∈ Q
    · simp only [g, dif_pos h]; exact hγs _ a
    · simp only [g, dif_neg h, Units.val_one, Matrix.one_mulVec]
  have hgz : ∀ q, (g q : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z = z := fun q => by
    by_cases h : q ∈ Q
    · simp only [g, dif_pos h]; exact hγz _
    · simp only [g, dif_neg h, Units.val_one, Matrix.one_mulVec]
  have hgloc : ∀ q ∈ Q, ∀ p : Ideal (𝓞 I.E), p.IsMaximal →
      p.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = q.asIdeal →
      ∀ v, v ∈ locE I p M ↔ ∃ w ∈ locE I p I.L, (g q : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ w = v := by
    intro q hq p hp hpq v
    have hc := Classical.choose_spec (hQex q hq)
    simp only [g, dif_pos hq]
    rw [loc_congr I hp hc.1 (hpq.trans hc.2.symm) M, loc_congr I hp hc.1 (hpq.trans hc.2.symm) I.L]
    exact hloc _ hc.1 v

  let Qs := hQ.toFinset
  let ε : HeightOneSpectrum (𝓞 I.F) → I.E ⊗[I.F] Af I.F := fun q => iA I (eT {q})
  let φ : I.E ⊗[I.F] Af I.F := iA I (eT Qᶜ)
  have horth : Orth Qs ε := fun i _ j _ => by
    simp only [ε]
    rw [← map_mul, eT_orth]
    split_ifs <;> simp
  have hφε : ∀ i ∈ Qs, φ * ε i = 0 := fun i hi => by
    simp only [φ, ε]
    rw [← map_mul, eT_compl_mul (hQ.mem_toFinset.1 hi), map_zero]
  have hsum : φ + ∑ i ∈ Qs, ε i = 1 := by
    simp only [φ, ε]
    rw [← map_sum, ← map_add, eT_sum hQ, map_one]

  let G : HeightOneSpectrum (𝓞 I.F) → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := fun q =>
    (g q : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))
  let Gi : HeightOneSpectrum (𝓞 I.F) → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := fun q =>
    (((g q)⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))
  have hGGi : ∀ q, G q * Gi q = 1 := fun q => by
    simp only [G, Gi]
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hGiG : ∀ q, Gi q * G q = 1 := fun q => by
    simp only [G, Gi]
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hXY : gl Qs ε 1 G * gl Qs ε 1 Gi = 1 := by
    rw [gl_mul horth]; simp only [hGGi, mul_one]; exact gl_const _ _ _
  have hYX : gl Qs ε 1 Gi * gl Qs ε 1 G = 1 := by
    rw [gl_mul horth]; simp only [hGiG, mul_one]; exact gl_const _ _ _

  let σR := Formalism.UG.sigR I.cm.sig (Af I.F)
  let J' := I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
  have hσε : ∀ i ∈ Qs, σR (ε i) = ε i := fun i _ => by
    simp only [σR, ε]
    rw [Algebra.TensorProduct.includeRight_apply]
    exact DictLat.sigR_one_tmul I _
  have hcG : ∀ q, Formalism.UG.cT σR (G q) =
      (Formalism.UG.cT (starRingEnd I.E) (g q : Matrix (Fin I.n) (Fin I.n) I.E)).map
        (Formalism.UG.inclE (F := I.F) (Af I.F)) := fun q => by
    ext a b
    simp only [Formalism.UG.cT, G, σR, Matrix.map_apply, Matrix.transpose_apply, DictLat.sigR_inclE, starRingEnd_apply]
  have hGu : ∀ q, Formalism.UG.cT σR (G q) * J' * G q = J' := fun q => by
    rw [hcG]
    simp only [G, J']
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun N => N.map (Formalism.UG.inclE (F := I.F) (Af I.F)))
      (show Formalism.UG.cT (starRingEnd I.E) (g q : Matrix (Fin I.n) (Fin I.n) I.E) * I.J *
        (g q : Matrix (Fin I.n) (Fin I.n) I.E) = I.J from hgU q)
  have hXU : Formalism.UG.cT σR (gl Qs ε 1 G) * J' * gl Qs ε 1 G = J' := by
    rw [cT_gl σR hσε, Formalism.UG.cT_one]
    conv_lhs => rw [show J' = gl Qs ε J' (fun _ => J') from (gl_const _ _ _).symm]
    rw [gl_mul horth, gl_mul horth]
    simp only [hGu, mul_one, one_mul]
    exact gl_const _ _ _
  let xg : GL (Fin I.n) (I.E ⊗[I.F] Af I.F) := ⟨gl Qs ε 1 G, gl Qs ε 1 Gi, hXY, hYX⟩
  have hxU : xg ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) := hXU
  let x : I.Gf := ⟨xg, hxU⟩
  have hfx : I.fmat x = gl Qs ε 1 G := rfl
  have hfxi : I.fmat x⁻¹ = gl Qs ε 1 Gi := rfl

  have hfix : ∀ u : Fin I.n → I.E, (∀ q, (g q : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u = u) →
      I.fmat x *ᵥ iv I u = iv I u := by
    intro u hu
    rw [hfx, gl_mulVec, Matrix.one_mulVec, Finset.sum_eq_zero (fun q _ => ?_), add_zero]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [G]
    rw [dictTop_map_mulVec, hu, sub_self, smul_zero]
  refine ⟨x, fun a => hfix _ (fun q => hgs q a), hfix _ hgz, ?_⟩

  ext v
  show I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf ↔ v ∈ M
  rw [hfxi]
  have hdec : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, y ∈ I.Lf ↔ φ • y ∈ I.Lf ∧ ∀ q ∈ Qs, ε q • y ∈ I.Lf := by
    intro y
    refine ⟨fun h => ⟨DictLat.Lf_smul I (iA_mem I (eT_mem _)) h,
      fun q _ => DictLat.Lf_smul I (iA_mem I (eT_mem _)) h⟩, fun ⟨h0, h1⟩ => ?_⟩
    have hy : y = φ • y + ∑ q ∈ Qs, ε q • y := by
      rw [← Finset.sum_smul, ← add_smul, hsum, one_smul]
    rw [hy]
    exact add_mem h0 (Submodule.sum_mem _ h1)
  have hproj : ∀ q ∈ Qs, ε q • (gl Qs ε 1 Gi *ᵥ iv I v) =
      ε q • iv I ((((g q)⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ v) := fun q hq => by
    rw [gl_proj horth _ _ _ hq]
    simp only [Gi]
    rw [dictTop_map_mulVec]
  have hproj0 : φ • (gl Qs ε 1 Gi *ᵥ iv I v) = φ • iv I v := by
    rw [gl_proj0 hφε, Matrix.one_mulVec]
  rw [hdec, hproj0]
  constructor
  · rintro ⟨h0, h1⟩
    refine Formalism.HermitianLatticesTheory.locBasic_lg (fun p => Formalism.HermitianLatticesTheory.hcompl (K := I.E) p)
      (fun p hp s hs => by have := hp.isPrime; exact Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem (K := I.E) p s hs)
      M v (fun p hp => ?_)
    show v ∈ locE I p M
    by_cases hq : under I p hp ∈ Q
    · have h2 := h1 _ (hQ.mem_toFinset.2 hq)
      rw [hproj _ (hQ.mem_toFinset.2 hq)] at h2
      obtain ⟨a, ha, haw⟩ := descent I (under I p hp) (eT_mem _) (eT_of_mem (Set.mem_singleton _)) _ h2
      rw [hgloc _ hq p hp rfl]
      exact ⟨_, (loc_iff I p hp _ _).2 ⟨a, ha, haw⟩,
        by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
    · obtain ⟨a, ha, haw⟩ := descent I (under I p hp) (eT_mem _) (eT_of_mem hq) _ h0
      have hne : locE I p M = locE I p I.L := by
        by_contra hne
        exact hq ⟨p, hp, hne, rfl⟩
      rw [hne]
      exact (loc_iff I p hp _ _).2 ⟨a, ha, haw⟩
  · intro hv
    refine ⟨?_, fun q hq => ?_⟩
    · apply glue I Qᶜ v
      intro q hq
      have hker : RingHom.ker (algebraMap (𝓞 I.F) (𝓞 I.E)) ≤ q.asIdeal := by
        rw [(RingHom.injective_iff_ker_eq_bot _).1 (alg_inj I)]
        exact bot_le
      obtain ⟨p, hp, hpq⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 I.E) q.asIdeal hker
      have hne : locE I p M = locE I p I.L := by
        by_contra hne
        exact hq ⟨p, hp, hne, hpq⟩
      have h3 : v ∈ locE I p M := Formalism.HermitianLatticesTheory.locBasic_le_locS _ M hv
      rw [hne] at h3
      obtain ⟨a, ha, haw⟩ := (loc_iff I p hp _ _).1 h3
      exact ⟨a, hpq ▸ ha, haw⟩
    · rw [hproj q hq]
      apply glue I {q} _
      intro q' hq'
      rw [Set.mem_singleton_iff] at hq'
      subst hq'
      have hqQ := hQ.mem_toFinset.1 hq
      obtain ⟨p, hp, hpq⟩ := hQex q' hqQ
      obtain ⟨w, hw, hgw⟩ := (hgloc q' hqQ p hp hpq v).1 (Formalism.HermitianLatticesTheory.locBasic_le_locS _ M hv)
      have hw' : w = (((g q')⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ v := by
        rw [← hgw, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      obtain ⟨a, ha, haw⟩ := (loc_iff I p hp _ _).1 hw
      exact ⟨a, hpq ▸ ha, hw' ▸ haw⟩

end Formalism.L2.SG.Pf.LatDictZ.Z5
