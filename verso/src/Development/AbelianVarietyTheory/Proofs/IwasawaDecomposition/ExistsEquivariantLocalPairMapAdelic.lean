import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPairMovedOfMultipliesLocalFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalUnitaryPairToPairComponentMemLocalLevelStatement

noncomputable section

namespace GlobalTheory.LevelHecke

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

/- English proof (translation)
Rewrite `hh` using `[S.UlocAlt v hv]`. Take `⟨hg, h2⟩` from `(Subgroup.mem_inf.1 hh).2`. Conclude with `⟨hg, fun x => by rw [one_smul]; exact h2 x⟩`.
-/
theorem pm_mulsF_of_mem (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (h : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hh : h ∈ S.Uloc v) : MulsF S v hv 1 h := by
  rw [S.UlocAlt v hv] at hh
  obtain ⟨hg, h2⟩ := (Subgroup.mem_inf.1 hh).2
  exact ⟨hg, fun x => by rw [one_smul]; exact h2 x⟩

/- English proof (translation)
Take `⟨ha, ha'⟩` from `hg`. Take `⟨hb, hb'⟩` from `hh`. Use `⟨Subgroup.mul_mem _ ha hb, fun x => ?_⟩` and prove the remaining obligations. Establish `h1` using `ha' ⟨h.1 *ᵥ x.1, (hb x.1).1 x.2⟩`. Establish `h2` using `hb' x`.

Rewrite using `[← h2, ← h1, mul_smul]`. Use `congr 3`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[Matrix.mulVec_mulVec]`.
-/
theorem pm_mulsF_mul (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {a b : ℤ} {g h : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hg : MulsF S v hv a g) (hh : MulsF S v hv b h) :
    MulsF S v hv (b * a) (g * h) := by
  obtain ⟨ha, ha'⟩ := hg
  obtain ⟨hb, hb'⟩ := hh
  refine ⟨Subgroup.mul_mem _ ha hb, fun x => ?_⟩
  have h1 := ha' ⟨h.1 *ᵥ x.1, (hb x.1).1 x.2⟩
  have h2 := hb' x
  rw [← h2, ← h1, mul_smul]
  congr 3
  apply Subtype.ext
  simp [Matrix.mulVec_mulVec]

/- English proof (translation)
Establish `hpres : ∀ x : GA σ J, ∃ (c : C) (γ : GL (Fin n) E) (κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), γ ∈ UJ (σ : E →+* E) J ∧ κ ∈ S.U ∧ x.1 = bc (inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ := by`. Introduce `x`. Take `⟨c, hc⟩` from `hy (Quotient.mk'' x)`. Take `⟨hh', hhm, kk, hkm, heq⟩` from `(DoubleCoset.eq _ _ _ _).1 hc`. Take `⟨γ, hγ, hγe⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhm)`.

Use `⟨c, γ, kk.1, hγ, Subgroup.mem_subgroupOf.1 hkm, ?_⟩` and prove the remaining obligations. Rewrite using `[heq, Subgroup.coe_mul, Subgroup.coe_mul, ← hγe]`. Use `choose cc gg kk hgg hkk hx using hpres`. Establish `hloc : ∀ κ ∈ S.U, bc (prV (E` using `E) v) κ ∈ S.Uloc v := fun κ hκ => ((S.U_eq κ).1 hκ).2 v`. Establish `hmov : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' δ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), bc (inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ * δ → bc (prV (E := E) v) ((y c).1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ⁻¹ * γ') * (y c').1) = bc (prV (E := E) v) κ * bc (prV (E := E) v) δ * (bc (prV …`.

Introduce `c c' γ γ' κ κ' δ h`. Rewrite using `[← map_inv, ← map_mul, ← map_mul, map_mul (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))), map_inv]`. Use `congr 1`. Establish `h'` using `eq_mul_inv_of_mul_eq h`. Rewrite using `[mul_assoc, mul_assoc, h']`.

Use `group`. Establish `hact : ∀ (c' : C) (γ γ' : GL (Fin n) E), ((q c').act (glE (γ⁻¹ * γ'))).act (glE γ) = (q c').act (glE γ')`. Introduce `c' γ γ'`. Rewrite using `[Pr.act_act, ← glE_mul, mul_inv_cancel_left]`. Establish `key : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' δ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (a : ℤ), κ ∈ S.U → κ' ∈ S.U → bc (inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ * δ → MulsF S v hv a (bc (prV (E := E) v) δ) → (q c').act (glE γ') = ((q c).act (glE γ)).dil (a : k) := by`.

Introduce `c c' γ γ' κ κ' δ a hκ hκ' h hδ`. Establish `hm` using `pm_mulsF_mul S v hv (pm_mulsF_mul S v hv (pm_mulsF_of_mem S v hv _ (hloc κ hκ)) hδ) (pm_mulsF_of_mem S v hv _ (inv_mem (hloc κ' hκ')))`. Rewrite `hm` using `[one_mul, mul_one, ← hmov c c' γ γ' κ κ' δ h]`. Rewrite using `[← hact c' γ γ', h1 c c' _ a hm, Pr.act_dil]`. Establish `key1 : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), κ ∈ S.U → κ' ∈ S.U → bc (inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ → (q c').act (glE γ') = (q c).act (glE γ) := by`.

Introduce `c c' γ γ' κ κ' hκ hκ' h`. Use `key c c' γ γ' κ κ' 1 1 hκ hκ' (by rw [h, mul_one]) (pm_mulsF_of_mem S v hv _ (by rw [map_one]; exact one_mem _))` as an intermediate fact. Rewrite `this` using `[Int.cast_one, Pr.dil_one]`. Then use the resulting hypothesis. Use `⟨fun x => (q (cc x)).act (glE (gg x)), ⟨fun γ _ x x' h => ?_, fun x δ => ⟨fun h => ?_, fun h => ?_⟩, fun x δ a h => ?_⟩, fun c => ?_, fun x => ⟨_, _, rfl⟩⟩` and prove the remaining obligations. Use `show (q (cc x')).act _ = ((q (cc x)).act _).act _`.

Rewrite using `[Pr.act_act, ← glE_mul]`. Use `key1 _ _ _ _ (kk x) (kk x') (hkk x) (hkk x') ?_` and prove the remaining obligations. Rewrite using `[← hx x', h, map_mul]`. Use `conv_lhs => rw [hx x]`. Simplify using `only [mul_assoc]`.

Establish `h' : (q (cc (x * δ))).act (glE (gg (x * δ))) = (q (cc x)).act (glE (gg x))` using `h`. Rewrite `h'` using `[← hact _ (gg x)]`. Establish `h3` using `h2 _ _ _ (mul_mem (inv_mem (hgg x)) (hgg (x * δ))) (Pr.act_injective _ h')`. Rewrite `h3` using `[hmov _ _ _ _ (kk x) (kk (x * δ)) δ.1 (by rw [← hx x, ← hx (x * δ)]; rfl)]`. Establish `h4` using `mul_mem (mul_mem (inv_mem (hloc _ (hkk x))) h3) (hloc _ (hkk (x * δ)))`.

Rewrite `h4` using `[← mul_assoc, inv_mul_cancel_right, inv_mul_cancel_left]`. Then use the resulting hypothesis. Use `key _ _ _ _ (kk x) (kk (x * δ)) δ.1 1 (hkk x) (hkk (x * δ)) (by rw [← hx x, ← hx (x * δ)]; rfl) (pm_mulsF_of_mem S v hv _ h)` as an intermediate fact. Rewrite `this` using `[Int.cast_one, Pr.dil_one]`. Then use the resulting hypothesis. Conclude with `key _ _ _ _ (kk x) (kk (x * δ)) δ.1 a (hkk x) (hkk (x * δ)) (by rw [← hx x, ← hx (x * δ)]; rfl) h.2.2`. Use `key1 c (cc (y c)) 1 (gg (y c)) 1 (kk (y c)) (one_mem _) (hkk _) (by rw [← hx (y c), map_one, one_mul, mul_one])` as an intermediate fact.

Rewrite `this` using `[glE_one, Pr.act_refl]`. Then use the resulting hypothesis.
-/
theorem pm_gen (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : Type} [Field k] {C : Type} (y : C → GA σ J)
    (hy : Function.Surjective (fun c => (Quotient.mk'' (y c) : Cls S)))
    (q : C → Pr (𝓞 E) (Fin n → E) k)
    (h1 : ∀ (c c' : C) (γ : GL (Fin n) E) (a : ℤ), MulsF S v hv a (bc (prV (E := E) v)
      ((y c).1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c').1)) →
      (q c').act (glE γ) = (q c).dil (a : k))
    (h2 : ∀ (c c' : C) (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → (q c').act (glE γ) = q c →
      bc (prV (E := E) v) ((y c).1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c').1) ∈ S.Uloc v) :
    ∃ p : GA σ J → Pr (𝓞 E) (Fin n → E) k, PMap S v hv p ∧ (∀ c, p (y c) = q c) ∧
      ∀ x, ∃ c γ, p x = (q c).act (glE γ) := by
  have hpres : ∀ x : GA σ J, ∃ (c : C) (γ : GL (Fin n) E) (κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      γ ∈ UJ (σ : E →+* E) J ∧ κ ∈ S.U ∧
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ := by
    intro x
    obtain ⟨c, hc⟩ := hy (Quotient.mk'' x)
    obtain ⟨hh', hhm, kk, hkm, heq⟩ := (DoubleCoset.eq _ _ _ _).1 hc
    obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhm)
    refine ⟨c, γ, kk.1, hγ, Subgroup.mem_subgroupOf.1 hkm, ?_⟩
    rw [heq, Subgroup.coe_mul, Subgroup.coe_mul, ← hγe]
  choose cc gg kk hgg hkk hx using hpres
  have hloc : ∀ κ ∈ S.U, bc (prV (E := E) v) κ ∈ S.Uloc v := fun κ hκ => ((S.U_eq κ).1 hκ).2 v
  have hmov : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' δ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ * δ →
      bc (prV (E := E) v) ((y c).1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ⁻¹ * γ') * (y c').1) =
        bc (prV (E := E) v) κ * bc (prV (E := E) v) δ * (bc (prV (E := E) v) κ')⁻¹ := by
    intro c c' γ γ' κ κ' δ h
    rw [← map_inv, ← map_mul, ← map_mul, map_mul (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))), map_inv]
    congr 1
    have h' := eq_mul_inv_of_mul_eq h
    rw [mul_assoc, mul_assoc, h']
    group
  have hact : ∀ (c' : C) (γ γ' : GL (Fin n) E),
      ((q c').act (glE (γ⁻¹ * γ'))).act (glE γ) = (q c').act (glE γ') := by
    intro c' γ γ'
    rw [Pr.act_act, ← glE_mul, mul_inv_cancel_left]
  have key : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' δ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (a : ℤ),
      κ ∈ S.U → κ' ∈ S.U →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ * δ →
      MulsF S v hv a (bc (prV (E := E) v) δ) →
      (q c').act (glE γ') = ((q c).act (glE γ)).dil (a : k) := by
    intro c c' γ γ' κ κ' δ a hκ hκ' h hδ
    have hm := pm_mulsF_mul S v hv (pm_mulsF_mul S v hv (pm_mulsF_of_mem S v hv _ (hloc κ hκ)) hδ)
      (pm_mulsF_of_mem S v hv _ (inv_mem (hloc κ' hκ')))
    rw [one_mul, mul_one, ← hmov c c' γ γ' κ κ' δ h] at hm
    rw [← hact c' γ γ', h1 c c' _ a hm, Pr.act_dil]
  have key1 : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      κ ∈ S.U → κ' ∈ S.U →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ →
      (q c').act (glE γ') = (q c).act (glE γ) := by
    intro c c' γ γ' κ κ' hκ hκ' h
    have := key c c' γ γ' κ κ' 1 1 hκ hκ' (by rw [h, mul_one])
      (pm_mulsF_of_mem S v hv _ (by rw [map_one]; exact one_mem _))
    rwa [Int.cast_one, Pr.dil_one] at this
  refine ⟨fun x => (q (cc x)).act (glE (gg x)), ⟨fun γ _ x x' h => ?_, fun x δ => ⟨fun h => ?_, fun h => ?_⟩,
    fun x δ a h => ?_⟩, fun c => ?_, fun x => ⟨_, _, rfl⟩⟩
  · show (q (cc x')).act _ = ((q (cc x)).act _).act _
    rw [Pr.act_act, ← glE_mul]
    refine key1 _ _ _ _ (kk x) (kk x') (hkk x) (hkk x') ?_
    rw [← hx x', h, map_mul]
    conv_lhs => rw [hx x]
    simp only [mul_assoc]
  · have h' : (q (cc (x * δ))).act (glE (gg (x * δ))) = (q (cc x)).act (glE (gg x)) := h
    rw [← hact _ (gg x)] at h'
    have h3 := h2 _ _ _ (mul_mem (inv_mem (hgg x)) (hgg (x * δ))) (Pr.act_injective _ h')
    rw [hmov _ _ _ _ (kk x) (kk (x * δ)) δ.1 (by rw [← hx x, ← hx (x * δ)]; rfl)] at h3
    have h4 := mul_mem (mul_mem (inv_mem (hloc _ (hkk x))) h3) (hloc _ (hkk (x * δ)))
    rwa [← mul_assoc, inv_mul_cancel_right, inv_mul_cancel_left] at h4
  · have := key _ _ _ _ (kk x) (kk (x * δ)) δ.1 1 (hkk x) (hkk (x * δ)) (by rw [← hx x, ← hx (x * δ)]; rfl)
      (pm_mulsF_of_mem S v hv _ h)
    rwa [Int.cast_one, Pr.dil_one] at this
  · exact key _ _ _ _ (kk x) (kk (x * δ)) δ.1 a (hkk x) (hkk (x * δ)) (by rw [← hx x, ← hx (x * δ)]; rfl) h.2.2
  · have := key1 c (cc (y c)) 1 (gg (y c)) 1 (kk (y c)) (one_mem _) (hkk _)
      (by rw [← hx (y c), map_one, one_mul, mul_one])
    rwa [glE_one, Pr.act_refl] at this

end Gen

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D u A i hi P K fMe hF hJ v`. Take `⟨p, h1, h2, h3⟩` from `pm_gen K.lev (A.eV v).1 (A.eV v).2 K.y K.y_bij.2 (pc P v) (GlobalTheory.T.classPair_moved_of_multipliesLocalFunctional D u A i hi P K fMe hF v) (GlobalTheory.T.rationalUnitary_pairToPair_component_mem_localLevel D u A i hi P K fMe hF hJ v)`. Use `⟨p, h1, h2, fun x => ?_⟩` and prove the remaining obligations. Take `⟨c, γ, h⟩` from `h3 x`. Rewrite using `[h]`.

Conclude with `(pc_ok P v c).act _`.
-/
theorem exists_pmap : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → cT (sigD D : D.host.E →+* D.host.E) (gramN D i hi) = gramN D i hi → ∀ v : (D.mem u).A.vT, ∃ p : GA (sigD D) (gramN D i hi) → Pr (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) ((D.mem u).A.Fv v), PMap K.lev (A.eV v).1 (A.eV v).2 p ∧ (∀ c, p (K.y c) = pc P v c) ∧ ∀ x, (p x).Ok (A.res v) := by
  intro D u A i hi P K fMe hF hJ v
  obtain ⟨p, h1, h2, h3⟩ := pm_gen K.lev (A.eV v).1 (A.eV v).2 K.y K.y_bij.2 (pc P v)
    (GlobalTheory.T.classPair_moved_of_multipliesLocalFunctional D u A i hi P K fMe hF v) (GlobalTheory.T.rationalUnitary_pairToPair_component_mem_localLevel D u A i hi P K fMe hF hJ v)
  refine ⟨p, h1, h2, fun x => ?_⟩
  obtain ⟨c, γ, h⟩ := h3 x
  rw [h]
  exact (pc_ok P v c).act _

end GlobalTheory.LevelHecke

end
