import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjection
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.BlocksTwist

/- English proof (translation)
Establish `h' : IsUnit (M.map t)` using `by simpa using h.map (t.mapMatrix)`. Unfold `toG`. Rewrite using `[dif_pos h', dif_pos h]`. Use extensionality with `i j`. Simplify using `[gal]`.
-/
theorem toG_map {F : Type} [Field F] (t : F →+* F) {m : ℕ} (M : Matrix (Fin m) (Fin m) F) (h : IsUnit M) :
    toG (M.map t) = gal t m (toG M) := by
  have h' : IsUnit (M.map t) := by simpa using h.map (t.mapMatrix)
  unfold toG
  rw [dif_pos h', dif_pos h]
  ext i j
  simp [gal]

/- English proof (translation)
Simplify using `[gal]`.
-/
theorem coe_gal {F : Type} [Field F] (t : F →+* F) (n : ℕ) (p : GL (Fin n) F) :
    ((gal t n p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = (p : Matrix (Fin n) (Fin n) F).map t := by
  simp [gal]

/- English proof (translation)
Unfold `ent`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ent_map {F : Type} [Field F] (t : F →+* F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) :
    ent (M.map t) i j = t (ent M i j) := by
  unfold ent
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[tl, ent_map]`.
-/
theorem tl_map {F : Type} [Field F] (t : F →+* F) (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    tl a (M.map t) = (tl a M).map t := by
  ext i j; simp [tl, ent_map]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[br, ent_map]`.
-/
theorem br_map {F : Type} [Field F] (t : F →+* F) (a b : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    br a b (M.map t) = (br a b M).map t := by
  ext i j; simp [br, ent_map]

/- English proof (translation)
Introduce `i j hj hi`. Rewrite using `[coe_gal]`. Simplify using `[hp i j hj hi]`.
-/
theorem inPar_gal {F : Type} [Field F] (t : F →+* F) (a : ℕ) {n : ℕ} (p : GL (Fin n) F) (hp : InPar a p) :
    InPar a (gal t n p) := by
  intro i j hj hi
  rw [coe_gal]
  simp [hp i j hj hi]

/- English proof (translation)
Introduce `F _ t a b n hn p x hp hx`. Take `⟨H, π, hH, -, hπ, -, -⟩` from `BlockPar.block_par F a b n hn`. Set `p' : H` to `⟨p, (hH p).2 hp⟩`. Set `x' : H` to `⟨x, (hH x).2 hx⟩`. Set `g' : H` to `⟨gal t n p, (hH _).2 (inPar_gal t a p hp)⟩`.

Establish `key : π (p'⁻¹ * x' * g') = (π p')⁻¹ * π x' * π g'` using `by simp only [map_mul, map_inv]`. Rewrite `key` using `[hπ, hπ, hπ, hπ]`. Establish `e : ((p'⁻¹ * x' * g' : H) : GL (Fin n) F) = p⁻¹ * x * gal t n p` using `rfl`. Rewrite `key` using `[e]`. Establish `htl : tlG a (gal t n p) = gal t a (tlG a p)`.

Substitute `hn` using the available equality. Unfold `tlG`. Rewrite using `[coe_gal, tl_map, toG_map _ _ (BlockPar.units_of_par p hp).1]`. Establish `hbr : brG a b (gal t n p) = gal t b (brG a b p)`. Substitute `hn` using the available equality.

Unfold `brG`. Rewrite using `[coe_gal, br_map, toG_map _ _ (BlockPar.units_of_par p hp).2]`. Simplify using `only [Prod.ext_iff, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] at key`. Rewrite using `[← htl, ← hbr]`. Conclude with `key`.
-/
theorem blocks_twist : ∀ (F : Type) [Field F] (t : F →+* F) (a b n : ℕ), n = a + b → ∀ (p x : GL (Fin n) F), InPar a p → InPar a x → tlG a (p⁻¹ * x * gal t n p) = (tlG a p)⁻¹ * tlG a x * gal t a (tlG a p) ∧ brG a b (p⁻¹ * x * gal t n p) = (brG a b p)⁻¹ * brG a b x * gal t b (brG a b p) := by
  intro F _ t a b n hn p x hp hx
  obtain ⟨H, π, hH, -, hπ, -, -⟩ := BlockPar.block_par F a b n hn
  let p' : H := ⟨p, (hH p).2 hp⟩
  let x' : H := ⟨x, (hH x).2 hx⟩
  let g' : H := ⟨gal t n p, (hH _).2 (inPar_gal t a p hp)⟩
  have key : π (p'⁻¹ * x' * g') = (π p')⁻¹ * π x' * π g' := by simp only [map_mul, map_inv]
  rw [hπ, hπ, hπ, hπ] at key
  have e : ((p'⁻¹ * x' * g' : H) : GL (Fin n) F) = p⁻¹ * x * gal t n p := rfl
  rw [e] at key
  have htl : tlG a (gal t n p) = gal t a (tlG a p) := by
    subst hn
    unfold tlG
    rw [coe_gal, tl_map, toG_map _ _ (BlockPar.units_of_par p hp).1]
  have hbr : brG a b (gal t n p) = gal t b (brG a b p) := by
    subst hn
    unfold brG
    rw [coe_gal, br_map, toG_map _ _ (BlockPar.units_of_par p hp).2]
  simp only [Prod.ext_iff, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] at key
  rw [← htl, ← hbr]
  exact key

end GlobalTheory.Shin.BlocksTwist
