import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LongWConjApply
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WhitHered Matrix

namespace GlobalTheory.WhitHered

/- English proof (translation)
Use `set e' := stdBlocks (fun b => m (Fin.revPerm b)) (sum_rev_eq m hN) with he'`. Establish `key : ∀ (b b' : Fin c) (i' : Fin (m (Fin.revPerm b))) (j' : Fin (m (Fin.revPerm b'))), (((longW m hN k)⁻¹ * leviEmb k (stdBlocks m hN) t * longW m hN k : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e' ⟨b, i'⟩) (e' ⟨b', j'⟩) = (leviEmb k (stdBlocks m hN) t : Matrix (Fin N) (Fin N) …`. Introduce `b b' i' j'`. Rewrite using `[longW_conj_apply, he', revPlace_apply, revPlace_apply]`. Rewrite using `[mem_unipB]`.

Prove the components needed by the constructor for the conclusion. Introduce `i j hji`. Take `⟨⟨b, i'⟩, rfl⟩` from `e'.surjective i`. Take `⟨⟨b', j'⟩, rfl⟩` from `e'.surjective j`. Rewrite using `[key]`.

Distinguish the cases in `hb : b = b'`. Substitute `hb` using the available equality. Rewrite using `[leviEmb_apply_same]`. Establish `hlt : j' < i'`. Establish `h1` using `stdBlocks_val (fun b => m (Fin.revPerm b)) (sum_rev_eq m hN) b i'`.

Establish `h2` using `stdBlocks_val (fun b => m (Fin.revPerm b)) (sum_rev_eq m hN) b j'`. Establish `: ((e' ⟨b, j'⟩ : Fin N) : ℕ) < (e' ⟨b, i'⟩ : Fin N)` using `hji`. Rewrite `this` using `[he', h1, h2]`. Conclude with `Fin.lt_def.2 (by omega)`. Conclude with `((mem_unipB k).1 (ht (Fin.revPerm b))).1 i' j' hlt`.

Conclude with `leviEmb_apply_ne k (stdBlocks m hN) t (fun h => hb (Fin.revPerm.injective h)) i' j'`. Introduce `i`. Take `⟨⟨b, i'⟩, rfl⟩` from `e'.surjective i`. Rewrite using `[key, leviEmb_apply_same]`. Conclude with `((mem_unipB k).1 (ht (Fin.revPerm b))).2 i'`.
-/
theorem longW_conj_leviEmb_mem_unipB {k : Type} [Field k] {N c : ℕ} {m : Fin c → ℕ} (hN : ∑ a, m a = N)
    (t : Levi k fun a => Fin (m a)) (ht : ∀ a, t a ∈ unipB k (Fin (m a))) :
    (longW m hN k)⁻¹ * leviEmb k (stdBlocks m hN) t * longW m hN k ∈ unipB k (Fin N) := by
  set e' := stdBlocks (fun b => m (Fin.revPerm b)) (sum_rev_eq m hN) with he'
  have key : ∀ (b b' : Fin c) (i' : Fin (m (Fin.revPerm b))) (j' : Fin (m (Fin.revPerm b'))),
      (((longW m hN k)⁻¹ * leviEmb k (stdBlocks m hN) t * longW m hN k : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) (e' ⟨b, i'⟩) (e' ⟨b', j'⟩) =
      (leviEmb k (stdBlocks m hN) t : Matrix (Fin N) (Fin N) k)
        (stdBlocks m hN ⟨Fin.revPerm b, i'⟩) (stdBlocks m hN ⟨Fin.revPerm b', j'⟩) := by
    intro b b' i' j'
    rw [longW_conj_apply, he', revPlace_apply, revPlace_apply]
  rw [mem_unipB]
  constructor
  · intro i j hji
    obtain ⟨⟨b, i'⟩, rfl⟩ := e'.surjective i
    obtain ⟨⟨b', j'⟩, rfl⟩ := e'.surjective j
    rw [key]
    by_cases hb : b = b'
    · subst hb
      rw [leviEmb_apply_same]
      have hlt : j' < i' := by
        have h1 := stdBlocks_val (fun b => m (Fin.revPerm b)) (sum_rev_eq m hN) b i'
        have h2 := stdBlocks_val (fun b => m (Fin.revPerm b)) (sum_rev_eq m hN) b j'
        have : ((e' ⟨b, j'⟩ : Fin N) : ℕ) < (e' ⟨b, i'⟩ : Fin N) := hji
        rw [he', h1, h2] at this
        exact Fin.lt_def.2 (by omega)
      exact ((mem_unipB k).1 (ht (Fin.revPerm b))).1 i' j' hlt
    · exact leviEmb_apply_ne k (stdBlocks m hN) t (fun h => hb (Fin.revPerm.injective h)) i' j'
  · intro i
    obtain ⟨⟨b, i'⟩, rfl⟩ := e'.surjective i
    rw [key, leviEmb_apply_same]
    exact ((mem_unipB k).1 (ht (Fin.revPerm b))).2 i'

/- English proof (translation)
Introduce `hN t ht` and use `longW_conj_leviEmb_mem_unipB hN t ht`.
-/
example : ∀ {k : Type} [Field k] {N c : ℕ} {m : Fin c → ℕ} (hN : ∑ a, m a = N) (t : Levi k fun a => Fin (m a)), (∀ a, t a ∈ unipB k (Fin (m a))) → (longW m hN k)⁻¹ * leviEmb k (stdBlocks m hN) t * longW m hN k ∈ unipB k (Fin N) :=
  fun hN t ht => longW_conj_leviEmb_mem_unipB hN t ht

end GlobalTheory.WhitHered
