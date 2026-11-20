import Mathlib

namespace GlobalTheory.DoubleCosetWeight

open Subgroup

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [mem_inf, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxT, y, hy, rfl⟩`. Use `⟨q * (k * y * k⁻¹) * q⁻¹, ⟨?_, k * y * k⁻¹, K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk), rfl⟩, ?_⟩` and prove the remaining obligations.

Establish `: q * (k * y * k⁻¹) * q⁻¹ = t⁻¹ * (t * q * k * y * (t * q * k)⁻¹) * t` using `by group`. Rewrite using `[this]`. Conclude with `T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht`. Use `group`. Introduce and unpack `⟨z, ⟨hzT, y, hy, rfl⟩, rfl⟩`.

Use `⟨T.mul_mem (T.mul_mem ht hzT) (T.inv_mem ht), k⁻¹ * y * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hy) hk, ?_⟩` and prove the remaining obligations. Use `group`.
-/
theorem inf_map_conj_mul_eq {G : Type} [Group G] (T K : Subgroup G) {t k : G}
    (ht : t ∈ T) (hk : k ∈ K) (q : G) :
    T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom =
      (T ⊓ K.map (MulAut.conj q).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
  ext x
  simp only [mem_inf, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hxT, y, hy, rfl⟩
    refine ⟨q * (k * y * k⁻¹) * q⁻¹, ⟨?_, k * y * k⁻¹, K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk), rfl⟩, ?_⟩
    · have : q * (k * y * k⁻¹) * q⁻¹ = t⁻¹ * (t * q * k * y * (t * q * k)⁻¹) * t := by group
      rw [this]; exact T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
    · group
  · rintro ⟨z, ⟨hzT, y, hy, rfl⟩, rfl⟩
    refine ⟨T.mul_mem (T.mul_mem ht hzT) (T.inv_mem ht), k⁻¹ * y * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hy) hk, ?_⟩
    group

def gen {G : Type} [Group G] (T K : Subgroup G) : Subgroup G :=
  ⨆ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom

/- English proof (translation)
Rewrite using `[map_le_iff_le_comap]`. Use `iSup_le fun q => ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[mem_comap]`. Establish `h1 : (MulAut.conj t).toMonoidHom x ∈ T ⊓ K.map (MulAut.conj (t * q * 1)).toMonoidHom`.

Rewrite using `[inf_map_conj_mul_eq T K ht K.one_mem q]`. Conclude with `mem_map_of_mem _ hx`. Conclude with `(le_iSup (fun q : G => T ⊓ K.map (MulAut.conj q).toMonoidHom) (t * q * 1)) h1`.
-/
theorem gen_map_le {G : Type} [Group G] (T K : Subgroup G) {t : G} (ht : t ∈ T) :
    (gen T K).map (MulAut.conj t).toMonoidHom ≤ gen T K := by
  rw [map_le_iff_le_comap]
  refine iSup_le fun q => ?_
  intro x hx
  rw [mem_comap]
  have h1 : (MulAut.conj t).toMonoidHom x ∈ T ⊓ K.map (MulAut.conj (t * q * 1)).toMonoidHom := by
    rw [inf_map_conj_mul_eq T K ht K.one_mem q]
    exact mem_map_of_mem _ hx
  exact (le_iSup (fun q : G => T ⊓ K.map (MulAut.conj q).toMonoidHom) (t * q * 1)) h1

/- English proof (translation)
Use `le_antisymm (gen_map_le T K ht) fun x hx => ?_` and prove the remaining obligations. Establish `: (MulAut.conj t⁻¹).toMonoidHom x ∈ gen T K` using `gen_map_le T K (T.inv_mem ht) (mem_map_of_mem _ hx)`. Use `⟨_, this, ?_⟩` and prove the remaining obligations. Simplify using `[MulAut.conj_apply, mul_assoc]`.
-/
theorem gen_map_eq {G : Type} [Group G] (T K : Subgroup G) {t : G} (ht : t ∈ T) :
    (gen T K).map (MulAut.conj t).toMonoidHom = gen T K := by
  refine le_antisymm (gen_map_le T K ht) fun x hx => ?_
  have : (MulAut.conj t⁻¹).toMonoidHom x ∈ gen T K :=
    gen_map_le T K (T.inv_mem ht) (mem_map_of_mem _ hx)
  refine ⟨_, this, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

/- English proof (translation)
Introduce `t ht k hk q`. Establish `hN : gen T K ≤ C` using `iSup_le hC`. Establish `hA : ∀ p : G, T ⊓ K.map (MulAut.conj p).toMonoidHom ≤ gen T K` using `fun p => le_iSup (fun q : G => T ⊓ K.map (MulAut.conj q).toMonoidHom) p`. Establish `e1` using `relIndex_mul_relIndex _ _ _ (hA (t * q * k)) hN`. Establish `e2` using `relIndex_mul_relIndex _ _ _ (hA q) hN`.

Rewrite using `[← e1, ← e2, inf_map_conj_mul_eq T K ht hk q]`. Use `congr 1`. Use `conv_lhs => rw [← gen_map_eq T K ht]`. Conclude with `relIndex_map_map_of_injective _ _ (MulAut.conj t).injective`.
-/
theorem relIndex_eq {G : Type} [Group G] (T C K : Subgroup G)
    (hC : ∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) :
    ∀ t ∈ T, ∀ k ∈ K, ∀ q : G,
      (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C =
        (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C := by
  intro t ht k hk q
  have hN : gen T K ≤ C := iSup_le hC
  have hA : ∀ p : G, T ⊓ K.map (MulAut.conj p).toMonoidHom ≤ gen T K := fun p =>
    le_iSup (fun q : G => T ⊓ K.map (MulAut.conj q).toMonoidHom) p
  have e1 := relIndex_mul_relIndex _ _ _ (hA (t * q * k)) hN
  have e2 := relIndex_mul_relIndex _ _ _ (hA q) hN
  rw [← e1, ← e2, inf_map_conj_mul_eq T K ht hk q]
  congr 1
  conv_lhs => rw [← gen_map_eq T K ht]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj t).injective

end GlobalTheory.DoubleCosetWeight

/- English proof (translation)
Introduce `G _ T C K hC` and use `GlobalTheory.DoubleCosetWeight.relIndex_eq T C K hC`.
-/
theorem GlobalTheory.doubleCoset_relIndex_const : ∀ (G : Type) [Group G] (T C K : Subgroup G), (∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) → ∀ t ∈ T, ∀ k ∈ K, ∀ q : G, (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C = (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C :=
  fun G _ T C K hC => GlobalTheory.DoubleCosetWeight.relIndex_eq T C K hC
