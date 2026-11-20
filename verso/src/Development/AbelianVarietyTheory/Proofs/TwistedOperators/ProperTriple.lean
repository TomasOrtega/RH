import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.ProperTriple

open MeasureTheory ValuativeRel Matrix in
/- English proof (translation)
Establish `h` using `_root_.GlobalTheory.RootEx.Model.mem_N_iff.1 hu`. Unfold `_root_.GlobalTheory.RootEx.InN _root_.GlobalTheory.RootEx.lev at h`. Use `⟨fun t t' => ?_, fun t i hi => ?_, fun t i hi => ?_⟩` and prove the remaining obligations. Rewrite using `[h _ _ (by simp)]`. Simplify using `[Matrix.one_apply]`.

Rewrite using `[h _ _ (by simp [hi])]`. Simplify using the standard rewrite rules. Rewrite using `[h _ _ (by simp [hi])]`. Simplify using the standard rewrite rules.
-/
private lemma unipotent_block_entries_eq_one_zero {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {c ρ : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ _root_.GlobalTheory.RootEx.N k n c (ρ + 1)) :
    (∀ t t' : n, (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl t) (Sum.inl t') =
      (1 : Matrix n n k) t t') ∧
    (∀ (t : n) (i : Fin c), (i : ℕ) + 1 = ρ + 1 →
      (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl t) (Sum.inr i) = 0) ∧
    (∀ (t : n) (i : Fin c), (i : ℕ) + 1 = ρ + 1 →
      (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inl t) = 0) := by
  have h := _root_.GlobalTheory.RootEx.Model.mem_N_iff.1 hu
  unfold _root_.GlobalTheory.RootEx.InN _root_.GlobalTheory.RootEx.lev at h
  refine ⟨fun t t' => ?_, fun t i hi => ?_, fun t i hi => ?_⟩
  · rw [h _ _ (by simp)]
    simp [Matrix.one_apply]
  · rw [h _ _ (by simp [hi])]
    simp
  · rw [h _ _ (by simp [hi])]
    simp

open MeasureTheory ValuativeRel Matrix in
/- English proof (translation)
Take `⟨hll, hlr, -⟩` from `unipotent_block_entries_eq_one_zero u.2`. Take `⟨hll', -, hrl'⟩` from `unipotent_block_entries_eq_one_zero (inv_mem u.2)`. Establish `h1 : ∀ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) * _root_.GlobalTheory.RootEx.colE c (ρ + 1) β) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩) = ((x : Matrix n n k) *ᵥ β) s`. Introduce `s`. Rewrite using `[Units.val_mul, Units.val_mul, _root_.GlobalTheory.RootEx.Radical.embX_val, _root_.GlobalTheory.RootEx.ExchangeSupport.colE_val]`.

Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, hll, hlr, _root_.GlobalTheory.RootEx.ExchangeSupport.colM, Matrix.mulVec, dotProduct, Matrix.one_apply]`. Establish `h2 : ∀ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) * _root_.GlobalTheory.RootEx.colE c (ρ + 1) β)⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl r) (Sum.inl s) = (↑x⁻¹ : Matrix n n k) r s`. Introduce `s`. Rewrite using `[_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← map_inv, _root_.GlobalTheory.RootEx.Radical.embX_val, _root_.GlobalTheory.RootEx.ExchangeSupport.colE_inv_val]`. Simplify using `only [Matrix.coe_units_inv] at hll' hrl' ⊢`.

Establish `hz : ∀ i : Fin c, (i : ℕ) = ρ → ∑ a, ((u : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)⁻¹ (Sum.inr i) (Sum.inl a) * (↑x : Matrix n n k)⁻¹ a s = 0` using `fun i hi => Finset.sum_eq_zero fun a _ => by rw [hrl' a i (by omega), zero_mul]`. Simplify using `+contextual [Matrix.mul_apply, Fintype.sum_sum_type, hll', _root_.GlobalTheory.RootEx.ExchangeSupport.colM, Matrix.one_apply, hz]`. Repeatedly rewrite using `[h1, h2]`. Express the relevant statement in the definitionally equal form `((↑x⁻¹ : Matrix n n k) *ᵥ ((x : Matrix n n k) *ᵥ β)) r = β r`. Rewrite using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`.
-/
private lemma recover_colE_vec_from_embX_product {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {c ρ : ℕ} (hρc : ρ < c) (x : GL n k) (u : _root_.GlobalTheory.RootEx.N k n c (ρ + 1))
    (β : n → k) (r : n) :
    ∑ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
        _root_.GlobalTheory.RootEx.colE c (ρ + 1) β)⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl r) (Sum.inl s) *
      (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
        _root_.GlobalTheory.RootEx.colE c (ρ + 1) β) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩) = β r := by
  obtain ⟨hll, hlr, -⟩ := unipotent_block_entries_eq_one_zero u.2
  obtain ⟨hll', -, hrl'⟩ := unipotent_block_entries_eq_one_zero (inv_mem u.2)
  have h1 : ∀ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
      _root_.GlobalTheory.RootEx.colE c (ρ + 1) β) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩) = ((x : Matrix n n k) *ᵥ β) s := by
    intro s
    rw [Units.val_mul, Units.val_mul, _root_.GlobalTheory.RootEx.Radical.embX_val,
      _root_.GlobalTheory.RootEx.ExchangeSupport.colE_val]
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hll, hlr, _root_.GlobalTheory.RootEx.ExchangeSupport.colM,
      Matrix.mulVec, dotProduct, Matrix.one_apply]
  have h2 : ∀ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
      _root_.GlobalTheory.RootEx.colE c (ρ + 1) β)⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl r) (Sum.inl s) = (↑x⁻¹ : Matrix n n k) r s := by
    intro s
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← map_inv,
      _root_.GlobalTheory.RootEx.Radical.embX_val, _root_.GlobalTheory.RootEx.ExchangeSupport.colE_inv_val]
    simp only [Matrix.coe_units_inv] at hll' hrl' ⊢
    have hz : ∀ i : Fin c, (i : ℕ) = ρ →
        ∑ a, ((u : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)⁻¹ (Sum.inr i) (Sum.inl a) *
          (↑x : Matrix n n k)⁻¹ a s = 0 :=
      fun i hi => Finset.sum_eq_zero fun a _ => by rw [hrl' a i (by omega), zero_mul]
    simp +contextual [Matrix.mul_apply, Fintype.sum_sum_type, hll', _root_.GlobalTheory.RootEx.ExchangeSupport.colM,
      Matrix.one_apply, hz]
  simp_rw [h1, h2]
  change ((↑x⁻¹ : Matrix n n k) *ᵥ ((x : Matrix n n k) *ᵥ β)) r = β r
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

open MeasureTheory ValuativeRel Matrix in

/- English proof (translation)
Introduce `k _ _ _ _ n _ _ c ρ _ hρc C hC`. Set `F : GL (n ⊕ Fin c) k → (n → k)` to `fun g r => ∑ s, (↑g⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl r) (Sum.inl s) * (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩)`. Establish `hF : Continuous F`. Use `continuous_pi fun r => continuous_finset_sum _ fun s _ => ?_` and prove the remaining obligations. Conclude with `(Units.continuous_coe_inv.matrix_elem _ _).mul (Units.continuous_val.matrix_elem _ _)`.

Establish `hK : IsCompact (F '' C)` using `hC.image hF`. Establish `hC' : IsCompact ((fun q : GL (n ⊕ Fin c) k × (n → k) => q.1 * (_root_.GlobalTheory.RootEx.colE c (ρ + 1) q.2)⁻¹) '' (C ×ˢ (F '' C)))` using `(hC.prod hK).image (continuous_fst.mul (_root_.GlobalTheory.RootEx.ExchangeSupport.continuous_colE.comp continuous_snd).inv)`. Take `⟨D₀, hD₀, hD₀C⟩` from `_root_.GlobalTheory.QuotInt.compact_preimage (_root_.GlobalTheory.RootEx.VolN.isClosed_N (k := k) (n := n) (c := c) (ρ + 1)) hC'`. Use `⟨(fun q : (GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1)) × (n → k) => (q.1.1, q.1.2, q.2)) '' (D₀ ×ˢ (F '' C)), (hD₀.prod hK).image (by fun_prop), ?_⟩` and prove the remaining obligations. Introduce `z hz`.

Establish `hβ : z.2.2 ∈ F '' C` using `⟨_, hz, funext (recover_colE_vec_from_embX_product hρc z.1 z.2.1 z.2.2)⟩`. Establish `hz' : (z.1, z.2.1) ∈ D₀` using `hD₀C _ ⟨(_, z.2.2), ⟨hz, hβ⟩, by simp⟩`. Conclude with `⟨((z.1, z.2.1), z.2.2), ⟨hz', hβ⟩, rfl⟩`.
-/
theorem _root_.GlobalTheory.RootEx.ProperTriple.proper_triple : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ)
    (_ : ρ < c) (C : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact C),
    ∃ D : Set (GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1) × (n → k)), IsCompact D ∧
      ∀ z : GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1) × (n → k),
        _root_.GlobalTheory.RootEx.embX c z.1 * (z.2.1 : GL (n ⊕ Fin c) k) *
          _root_.GlobalTheory.RootEx.colE c (ρ + 1) z.2.2 ∈ C → z ∈ D := by
  intro k _ _ _ _ n _ _ c ρ _ hρc C hC
  let F : GL (n ⊕ Fin c) k → (n → k) := fun g r =>
    ∑ s, (↑g⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl r) (Sum.inl s) *
      (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩)
  have hF : Continuous F := by
    refine continuous_pi fun r => continuous_finset_sum _ fun s _ => ?_
    exact (Units.continuous_coe_inv.matrix_elem _ _).mul (Units.continuous_val.matrix_elem _ _)
  have hK : IsCompact (F '' C) := hC.image hF
  have hC' : IsCompact ((fun q : GL (n ⊕ Fin c) k × (n → k) =>
      q.1 * (_root_.GlobalTheory.RootEx.colE c (ρ + 1) q.2)⁻¹) '' (C ×ˢ (F '' C))) :=
    (hC.prod hK).image (continuous_fst.mul
      (_root_.GlobalTheory.RootEx.ExchangeSupport.continuous_colE.comp continuous_snd).inv)
  obtain ⟨D₀, hD₀, hD₀C⟩ := _root_.GlobalTheory.QuotInt.compact_preimage
    (_root_.GlobalTheory.RootEx.VolN.isClosed_N (k := k) (n := n) (c := c) (ρ + 1)) hC'
  refine ⟨(fun q : (GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1)) × (n → k) =>
    (q.1.1, q.1.2, q.2)) '' (D₀ ×ˢ (F '' C)), (hD₀.prod hK).image (by fun_prop), ?_⟩
  intro z hz
  have hβ : z.2.2 ∈ F '' C := ⟨_, hz, funext (recover_colE_vec_from_embX_product hρc z.1 z.2.1 z.2.2)⟩
  have hz' : (z.1, z.2.1) ∈ D₀ := hD₀C _ ⟨(_, z.2.2), ⟨hz, hβ⟩, by simp⟩
  exact ⟨((z.1, z.2.1), z.2.2), ⟨hz', hβ⟩, rfl⟩

end GlobalTheory.RootEx.ProperTriple
