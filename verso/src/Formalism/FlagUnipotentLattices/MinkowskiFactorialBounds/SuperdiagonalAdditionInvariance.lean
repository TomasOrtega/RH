import Formalism.FlagUnipotentLattices.PairingOrthogonalComplement
import Formalism.SobolevGaussianKernels.KernelBoundRel

namespace Formalism.HermitianLatticeCounting.P.S4aux

open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset

/- English proof (translation)
Introduce `E _ _ V _ _ h z y T hz`. Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hz]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem projection_weight_formula : ProjW := by
  intro E _ _ V _ _ h z y T hz
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hz]; ring

/- English proof (translation)
Introduce `E _ _ V _ _ h O abelian₂ th w1 la1 la2 la2' hth hI h1 h2 h3`. Establish `key : h la1 la2' = h (w1 + la1) (la2' - la2)`. Simplify using `only [map_add, map_sub, LinearMap.add_apply, h1, h2, h3]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨key, ?_⟩` and prove the remaining obligations.

Introduce and unpack `hw ⟨w, hw', he⟩`. Use `⟨h (w1 + la1) w, hI _ hw _ hw', ?_⟩` and prove the remaining obligations. Rewrite using `[key, he, LinearMap.map_smulₛₗ, starRingEnd_apply, hth]`. Both sides reduce to the same expression.
-/
theorem pair_second_constant : PairingOrthogonalComplement := by
  intro E _ _ V _ _ h O abelian₂ th w1 la1 la2 la2' hth hI h1 h2 h3
  have key : h la1 la2' = h (w1 + la1) (la2' - la2) := by
    simp only [map_add, map_sub, LinearMap.add_apply, h1, h2, h3]; ring
  refine ⟨key, ?_⟩
  rintro hw ⟨w, hw', he⟩
  refine ⟨h (w1 + la1) w, hI _ hw _ hw', ?_⟩
  rw [key, he, LinearMap.map_smulₛₗ, starRingEnd_apply, hth]; rfl

/- English proof (translation)
Introduce `E _ _ V _ _ h O abelian₂ th x x' u y v s hH hL hu hs h1 h2 h3`. Establish `mv` using `Formalism.SL.Final.eichMove E V h x x' u s hH h1 h2 v h3`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mv]`. Use `module`.

Introduce and unpack `⟨w, hw, he⟩ ⟨d, hd, hk⟩`. Use `⟨w + d • (u + s • x), abelian₂.add_mem hw (hL d hd _ (abelian₂.add_mem hu hs)), ?_⟩` and prove the remaining obligations. Rewrite `he` using `[mv]`. Rewrite `he` using `[hk]`. Establish `: y + h v u • x + (v + h v u • x') = (y + (v + h v u • (x + x') - (th * d) • (u + s • x))) + (th * d) • (u + s • x)` using `by module`.

Rewrite using `[this, he]`. Use `module`. Rewrite using `[mv]`. Use `module`.
-/
theorem leakage_algebraic_identity : LeakAlg := by
  intro E _ _ V _ _ h O abelian₂ th x x' u y v s hH hL hu hs h1 h2 h3
  have mv := Formalism.SL.Final.eichMove E V h x x' u s hH h1 h2 v h3
  refine ⟨?_, ?_, ?_⟩
  · rw [mv]; module
  · rintro ⟨w, hw, he⟩ ⟨d, hd, hk⟩
    refine ⟨w + d • (u + s • x), abelian₂.add_mem hw (hL d hd _ (abelian₂.add_mem hu hs)), ?_⟩
    rw [mv] at he
    rw [hk] at he
    have : y + h v u • x + (v + h v u • x') = (y + (v + h v u • (x + x') - (th * d) • (u + s • x))) + (th * d) • (u + s • x) := by module
    rw [this, he]; module
  · rw [mv]; module

/- English proof (translation)
Introduce `E _ _ V _ _ h O abelian₂ th x u y y' s hL hu hs h1 h2 h3`. Establish `key : eich h x u s (y + y') = y + y' - h y' x • (u + s • x)`. Simplify using `only [eich, map_add, LinearMap.add_apply, h1, h2, h3]`. Use `module`. Use `⟨key, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨w, hw, he⟩ ⟨d, hd, hk⟩`. Use `⟨w - d • (u + s • x), abelian₂.sub_mem hw (hL d hd _ (abelian₂.add_mem hu hs)), ?_⟩` and prove the remaining obligations. Rewrite using `[key, he, hk]`. Use `module`. Introduce and unpack `⟨t, rfl⟩ ⟨d, hd, hk⟩ w hw he`.

Express the relevant statement in the definitionally equal form `eichLin h x u s w ∈ abelian₂`. Establish `h4 : (t : E) • eichLin h x u s w = (t : E) • (w - d • (u + s • x))`. Rewrite using `[← map_smul, he]`. Express the relevant statement in the definitionally equal form `eich h x u s (y + y') = _`. Rewrite using `[key, hk, ← he]`.

Use `module`. Establish `h5 : eichLin h x u s w = w - d • (u + s • x)`. Use `congrArg (fun z => ((t⁻¹ : Eˣ) : E) • z) h4` as an intermediate fact. Simplify `this` using `[smul_smul]`. Rewrite using `[h5]`.

Conclude with `abelian₂.sub_mem hw (hL d hd _ (abelian₂.add_mem hu hs))`.
-/
theorem move_second_coordinate : MoveY := by
  intro E _ _ V _ _ h O abelian₂ th x u y y' s hL hu hs h1 h2 h3
  have key : eich h x u s (y + y') = y + y' - h y' x • (u + s • x) := by
    simp only [eich, map_add, LinearMap.add_apply, h1, h2, h3]; module
  refine ⟨key, ?_, ?_⟩
  · rintro ⟨w, hw, he⟩ ⟨d, hd, hk⟩
    refine ⟨w - d • (u + s • x), abelian₂.sub_mem hw (hL d hd _ (abelian₂.add_mem hu hs)), ?_⟩
    rw [key, he, hk]; module
  · rintro ⟨t, rfl⟩ ⟨d, hd, hk⟩ w hw he
    change eichLin h x u s w ∈ abelian₂
    have h4 : (t : E) • eichLin h x u s w = (t : E) • (w - d • (u + s • x)) := by
      rw [← map_smul, he]; change eich h x u s (y + y') = _; rw [key, hk, ← he]; module
    have h5 : eichLin h x u s w = w - d • (u + s • x) := by
      have := congrArg (fun z => ((t⁻¹ : Eˣ) : E) • z) h4
      simpa [smul_smul] using this
    rw [h5]; exact abelian₂.sub_mem hw (hL d hd _ (abelian₂.add_mem hu hs))

/- English proof (translation)
Introduce `E _ _ V _ _ h r f co al u s J hco hal hf hu`. Establish `hx : ∀ i, h (f i) (∑ k, al k • f k) = 0`. Introduce `i`. Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.map_smulₛₗ]`. Distinguish the cases in `hk : k.val ≤ J.val`. Simplify using `[hf i k hk]`. Simplify using `[hal k (by omega)]`. Establish `hcx : ∀ k, co k (∑ i, al i • f i) = al k`.

Introduce `k`. Simplify using `[map_sum, hco]`. Establish `: ∀ j : Fin r, co j.castSucc (eich h (∑ i, al i • f i) u s (f j.succ)) = h (f j.succ) u * al j.castSucc`. Introduce `j`. Simplify using `only [eich, hx, zero_smul, sub_zero, map_add, map_smul, hcx, hco, smul_eq_mul]`.

Establish `: j.succ ≠ j.castSucc`. Introduce `hh`. Use `congrArg Fin.val hh` as an intermediate fact. Simplify using `at this`. Simplify using `[this]`.

Simplify using `only [this]`. Rewrite using `[Finset.sum_eq_single J]`. Expand and normalize the polynomial expressions, which then agree. Introduce `j _ hj`. Break down `lt_or_gt_of_ne (fun hh => hj (Fin.ext hh) : j.val ≠ J.val) with hlt | hgt` into its components or cases.

Rewrite using `[hu j.succ (by simp; omega)]; ring`. Rewrite using `[hal j.castSucc (by simpa using hgt)]; ring`. Simplify using the standard rewrite rules.
-/
theorem move_preserves_weight : MoveWeight := by
  intro E _ _ V _ _ h r f co al u s J hco hal hf hu
  have hx : ∀ i, h (f i) (∑ k, al k • f k) = 0 := by
    intro i
    rw [map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [LinearMap.map_smulₛₗ]
    by_cases hk : k.val ≤ J.val
    · simp [hf i k hk]
    · simp [hal k (by omega)]
  have hcx : ∀ k, co k (∑ i, al i • f i) = al k := by
    intro k; simp [map_sum, hco]
  have : ∀ j : Fin r, co j.castSucc (eich h (∑ i, al i • f i) u s (f j.succ)) = h (f j.succ) u * al j.castSucc := by
    intro j
    simp only [eich, hx, zero_smul, sub_zero, map_add, map_smul, hcx, hco, smul_eq_mul]
    have : j.succ ≠ j.castSucc := by
      intro hh; have := congrArg Fin.val hh; simp at this
    simp [this]
  simp only [this]
  rw [Finset.sum_eq_single J]
  · ring
  · intro j _ hj
    rcases lt_or_gt_of_ne (fun hh => hj (Fin.ext hh) : j.val ≠ J.val) with hlt | hgt
    · rw [hu j.succ (by simp; omega)]; ring
    · rw [hal j.castSucc (by simpa using hgt)]; ring
  · simp

/- English proof (translation)
Introduce `E _ _ V _ _ h O abelian₂ th x x' u s hH hth hL hI hu hs hb hxx h1 h2 v hv hvx`. Take `⟨w, hw, he⟩` from `hb`. Take `⟨d2, hd2, hk2⟩` from `hxx`. Establish `e1 : h v x = h v (x + x')` using `by simp [hvx]`. Establish `e2 : h v x = th * h v w` using `by rw [e1, he, LinearMap.map_smulₛₗ, starRingEnd_apply, hth]; rfl`.

Establish `mv` using `Formalism.SL.Final.eichMove E V h x x' u s hH h1 h2 v hvx`. Use `⟨e1, ⟨_, hI v hv w hw, e2⟩, ⟨h v w + h v u * d2, O.add_mem (hI v hv w hw) (O.mul_mem (hI v hv u hu) hd2), ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[e2, hk2]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨h v u • w - (h v w + h v u * d2) • (u + s • x), abelian₂.sub_mem (hL _ (hI v hv u hu) _ hw) (hL _ (O.add_mem (hI v hv w hw) (O.mul_mem (hI v hv u hu) hd2)) _ (abelian₂.add_mem hu hs)), ?_⟩` and prove the remaining obligations.

Rewrite using `[mv, he, e2, hk2]`. Use `module`.
-/
theorem move_congruence : MoveCong := by
  intro E _ _ V _ _ h O abelian₂ th x x' u s hH hth hL hI hu hs hb hxx h1 h2 v hv hvx
  obtain ⟨w, hw, he⟩ := hb
  obtain ⟨d2, hd2, hk2⟩ := hxx
  have e1 : h v x = h v (x + x') := by simp [hvx]
  have e2 : h v x = th * h v w := by rw [e1, he, LinearMap.map_smulₛₗ, starRingEnd_apply, hth]; rfl
  have mv := Formalism.SL.Final.eichMove E V h x x' u s hH h1 h2 v hvx
  refine ⟨e1, ⟨_, hI v hv w hw, e2⟩, ⟨h v w + h v u * d2, O.add_mem (hI v hv w hw) (O.mul_mem (hI v hv u hu) hd2), ?_⟩, ?_⟩
  · rw [e2, hk2]; ring
  · refine ⟨h v u • w - (h v w + h v u * d2) • (u + s • x), abelian₂.sub_mem (hL _ (hI v hv u hu) _ hw) (hL _ (O.add_mem (hI v hv w hw) (O.mul_mem (hI v hv u hu) hd2)) _ (abelian₂.add_mem hu hs)), ?_⟩
    rw [mv, he, e2, hk2]; module

/- English proof (translation)
Introduce `E _ _ V _ _ h O abelian₂ th x x' u s hH hL hI hxx hux hux' hs ⟨⟨w, hw, he⟩, hu, hsx, hssx, ⟨d, hd, hk⟩⟩`. Establish `inv` using `Formalism.SL.Final.eichInv E V h x u s hH hxx hux hs`. Establish `iso` using `Formalism.SL.Final.eichIsom E V h x u s hH hxx hux hs`. Establish `hxu : h x u = 0` using `by rw [hH u x, hux, star_zero]`. Establish `hx'u : h x' u = 0` using `by rw [hH u x', hux', star_zero]`.

Establish `nx : eich h x u s x = x` using `by simp [eich, hxu, hxx]`. Establish `nb : eich h x u s (x + x') = th • (w - d • (u + s • x))`. Simplify using `only [eich, map_add, LinearMap.add_apply, hxu, hxx, hx'u, hk]`. Rewrite using `[he]`. Use `module`.

Establish `mem : ∀ v, v ∈ moved h x u s abelian₂ ↔ eich h x u s v ∈ abelian₂` using `fun v => Iff.rfl`. Establish `lin : ∀ (c : E) v, eich h x u s (c • v) = c • eich h x u s v` using `fun c v => (eichLin h x u s).map_smul c v`. Establish `lin' : ∀ (c : E) v, eich h x (-u) (star s) (c • v) = c • eich h x (-u) (star s) v` using `fun c v => (eichLin h x (-u) (star s)).map_smul c v`. Use `⟨⟨⟨eich h x (-u) (star s) (w - d • (u + s • x)), ?_, ?_⟩, ?_, ?_, ?_, ⟨d, hd, hk⟩⟩, ?_, ?_, ?_, neg_neg u, star_star s⟩` and prove the remaining obligations. Rewrite using `[mem, (inv _).2]`.

Conclude with `abelian₂.sub_mem hw (hL d hd _ (abelian₂.add_mem hu hsx))`. Rewrite using `[← lin', ← nb, (inv _).1]`. Rewrite using `[mem]`. Establish `: eich h x u s (-u) = -(u + (s • x + star s • x))`. Simplify using `only [eich, map_neg, LinearMap.neg_apply, hux, ← hs]`.

Use `module`. Rewrite using `[this]`. Conclude with `abelian₂.neg_mem (abelian₂.add_mem hu (abelian₂.add_mem hsx hssx))`. Rewrite using `[mem, lin, nx]`. Conclude with `hssx`.

Rewrite using `[mem, lin, nx, star_star]`. Conclude with `hsx`. Introduce `a ha v hv`. Rewrite `hv`, the goal using `[mem]`. Rewrite using `[lin]`.

Conclude with `hL a ha _ hv`. Introduce `v hv v' hv'`. Rewrite using `[← iso v v']`. Conclude with `hI _ hv _ hv'`. Use extensionality with `v`.

Express the relevant statement in the definitionally equal form `eich h x u s (eich h x (-u) (star s) v) ∈ abelian₂ ↔ v ∈ abelian₂`. Rewrite using `[(inv v).2]`.
-/
theorem move_involutive : MoveInvol := by
  intro E _ _ V _ _ h O abelian₂ th x x' u s hH hL hI hxx hux hux' hs ⟨⟨w, hw, he⟩, hu, hsx, hssx, ⟨d, hd, hk⟩⟩
  have inv := Formalism.SL.Final.eichInv E V h x u s hH hxx hux hs
  have iso := Formalism.SL.Final.eichIsom E V h x u s hH hxx hux hs
  have hxu : h x u = 0 := by rw [hH u x, hux, star_zero]
  have hx'u : h x' u = 0 := by rw [hH u x', hux', star_zero]
  have nx : eich h x u s x = x := by simp [eich, hxu, hxx]
  have nb : eich h x u s (x + x') = th • (w - d • (u + s • x)) := by
    simp only [eich, map_add, LinearMap.add_apply, hxu, hxx, hx'u, hk]
    rw [he]; module
  have mem : ∀ v, v ∈ moved h x u s abelian₂ ↔ eich h x u s v ∈ abelian₂ := fun v => Iff.rfl
  have lin : ∀ (c : E) v, eich h x u s (c • v) = c • eich h x u s v := fun c v => (eichLin h x u s).map_smul c v
  have lin' : ∀ (c : E) v, eich h x (-u) (star s) (c • v) = c • eich h x (-u) (star s) v :=
    fun c v => (eichLin h x (-u) (star s)).map_smul c v
  refine ⟨⟨⟨eich h x (-u) (star s) (w - d • (u + s • x)), ?_, ?_⟩, ?_, ?_, ?_, ⟨d, hd, hk⟩⟩, ?_, ?_, ?_, neg_neg u, star_star s⟩
  · rw [mem, (inv _).2]; exact abelian₂.sub_mem hw (hL d hd _ (abelian₂.add_mem hu hsx))
  · rw [← lin', ← nb, (inv _).1]
  · rw [mem]
    have : eich h x u s (-u) = -(u + (s • x + star s • x)) := by
      simp only [eich, map_neg, LinearMap.neg_apply, hux, ← hs]; module
    rw [this]; exact abelian₂.neg_mem (abelian₂.add_mem hu (abelian₂.add_mem hsx hssx))
  · rw [mem, lin, nx]; exact hssx
  · rw [mem, lin, nx, star_star]; exact hsx
  · intro a ha v hv; rw [mem] at hv ⊢; rw [lin]; exact hL a ha _ hv
  · intro v hv v' hv'; rw [← iso v v']; exact hI _ hv _ hv'
  · ext v
    change eich h x u s (eich h x (-u) (star s) v) ∈ abelian₂ ↔ v ∈ abelian₂
    rw [(inv v).2]

/- English proof (translation)
Introduce `E _ _ V _ _ h O abelian₂ th x x' u s hH hth hL hI hxx hx'x' hux hux' hs hT`. Establish `hT'` using `hT`. Take `⟨⟨w, hw, he⟩, hu, hsx, hssx, ⟨d, hd, hk⟩⟩` from `hT`. Take `⟨⟨⟨w1, hw1, he1⟩, hu1, hsx1, hssx1, _⟩, hL1, hI1, hback, _, _⟩` from `move_involutive E V h O abelian₂ th x x' u s hH hL hI hxx hux hux' hs hT'`. Establish `inv'` using `Formalism.SL.Final.eichInv E V h x' u s hH hx'x' hux' hs`.

Establish `iso'` using `Formalism.SL.Final.eichIsom E V h x' u s hH hx'x' hux' hs`. Establish `inv` using `Formalism.SL.Final.eichInv E V h x u s hH hxx hux hs`. Establish `hx'u : h x' u = 0` using `by rw [hH u x', hux', star_zero]`. Establish `nx' : eich h x' u s x' = x'` using `by simp [eich, hx'u, hx'x']`. Establish `hkO : h x' x ∈ O` using `by rw [hk]; exact O.mul_mem hth hd`.

Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v0, ⟨hv0, hp⟩, rfl⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `eich h x u s (eich h x' u s v0) ∈ abelian₂`.

Conclude with `Formalism.SL.Final.eichInt E V h O abelian₂ x x' u s hH hL hI hu (by rw [he]; exact hL th hth _ hw) hsx hkO hux hux' v0 hv0 hp`. Establish `e : h (eich h x' u s v0) x' = h (eich h x' u s v0) (eich h x' u s x')` using `by rw [nx']`. Express the relevant statement in the definitionally equal form `h (eich h x' u s v0) x' = 0`. Rewrite using `[e, iso']`. Conclude with `hp`.

Introduce and unpack `⟨hv, hp⟩`. Use `⟨eich h x' (-u) (star s) v, ⟨?_, ?_⟩, (inv' v).2⟩` and prove the remaining obligations. Use `Formalism.SL.Final.eichInt E V h O (moved h x u s abelian₂) x x' (-u) (star s) hH hL1 hI1 hu1 (by rw [he1]; exact hL1 th hth _ hw1) hsx1 hkO (by simp [hux]) (by simp [hux']) v hv hp` as an intermediate fact. Express the relevant statement in the definitionally equal form `eich h x u s (eich h x (-u) (star s) (eich h x' (-u) (star s) v)) ∈ abelian₂ at this`. Rewrite `this` using `[(inv _).2]`. Then use the resulting hypothesis.

Establish `: h (eich h x' (-u) (star s) v) x' = h (eich h x' u s (eich h x' (-u) (star s) v)) (eich h x' u s x')` using `(iso' _ _).symm`. Rewrite using `[this, (inv' v).2, nx']`. Conclude with `hp`.
-/
theorem move_perpendicular : MovePerp := by
  intro E _ _ V _ _ h O abelian₂ th x x' u s hH hth hL hI hxx hx'x' hux hux' hs hT
  have hT' := hT
  obtain ⟨⟨w, hw, he⟩, hu, hsx, hssx, ⟨d, hd, hk⟩⟩ := hT
  obtain ⟨⟨⟨w1, hw1, he1⟩, hu1, hsx1, hssx1, _⟩, hL1, hI1, hback, _, _⟩ :=
    move_involutive E V h O abelian₂ th x x' u s hH hL hI hxx hux hux' hs hT'
  have inv' := Formalism.SL.Final.eichInv E V h x' u s hH hx'x' hux' hs
  have iso' := Formalism.SL.Final.eichIsom E V h x' u s hH hx'x' hux' hs
  have inv := Formalism.SL.Final.eichInv E V h x u s hH hxx hux hs
  have hx'u : h x' u = 0 := by rw [hH u x', hux', star_zero]
  have nx' : eich h x' u s x' = x' := by simp [eich, hx'u, hx'x']
  have hkO : h x' x ∈ O := by rw [hk]; exact O.mul_mem hth hd
  ext v
  constructor
  · rintro ⟨v0, ⟨hv0, hp⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · change eich h x u s (eich h x' u s v0) ∈ abelian₂
      exact Formalism.SL.Final.eichInt E V h O abelian₂ x x' u s hH hL hI hu (by rw [he]; exact hL th hth _ hw) hsx hkO hux hux' v0 hv0 hp
    · have e : h (eich h x' u s v0) x' = h (eich h x' u s v0) (eich h x' u s x') := by rw [nx']
      change h (eich h x' u s v0) x' = 0
      rw [e, iso']; exact hp
  · rintro ⟨hv, hp⟩
    refine ⟨eich h x' (-u) (star s) v, ⟨?_, ?_⟩, (inv' v).2⟩
    · have := Formalism.SL.Final.eichInt E V h O (moved h x u s abelian₂) x x' (-u) (star s) hH hL1 hI1 hu1
        (by rw [he1]; exact hL1 th hth _ hw1) hsx1 hkO (by simp [hux]) (by simp [hux']) v hv hp
      change eich h x u s (eich h x (-u) (star s) (eich h x' (-u) (star s) v)) ∈ abelian₂ at this
      rwa [(inv _).2] at this
    · have : h (eich h x' (-u) (star s) v) x' = h (eich h x' u s (eich h x' (-u) (star s) v)) (eich h x' u s x') := (iso' _ _).symm
      rw [this, (inv' v).2, nx']; exact hp

/- English proof (translation)
Introduce `E _ _ V _ _ h O abelian₂ th x x' hth hI ⟨w, hw, he⟩`. Use `⟨fun xi hxi h0 => ?_, fun xi hxi h0 => ?_⟩` and prove the remaining obligations. Establish `e : h xi x' = h xi (x + x')` using `by simp [h0]`. Conclude with `⟨e, h xi w, hI _ hxi _ hw, by rw [e, he, LinearMap.map_smulₛₗ, starRingEnd_apply, hth]; rfl⟩`. Establish `e : h x xi = h (x + x') xi` using `by simp [h0]`.

Conclude with `⟨e, h w xi, hI _ hw _ hxi, by rw [e, he]; simp⟩`.
-/
theorem type_class_count : TypeBeClass := by
  intro E _ _ V _ _ h O abelian₂ th x x' hth hI ⟨w, hw, he⟩
  refine ⟨fun xi hxi h0 => ?_, fun xi hxi h0 => ?_⟩
  · have e : h xi x' = h xi (x + x') := by simp [h0]
    exact ⟨e, h xi w, hI _ hxi _ hw, by rw [e, he, LinearMap.map_smulₛₗ, starRingEnd_apply, hth]; rfl⟩
  · have e : h x xi = h (x + x') xi := by simp [h0]
    exact ⟨e, h w xi, hI _ hw _ hxi, by rw [e, he]; simp⟩

/- English proof (translation)
Introduce `ι _ μ M ω e1 e2 hμ hrev hrow hM`. Establish `key : ∑ i, (μ i : ℂ) * ω i = ∑ i, (μ i : ℂ) * ∑ j, (M i j : ℂ) * ω j - ∑ i, (μ i : ℂ) * ω i * (((∑ j, M i j) - 1 : ℝ) : ℂ)`. Establish `: ∑ i, (μ i : ℂ) * ∑ j, (M i j : ℂ) * ω j = ∑ i, (μ i : ℂ) * ω i * ((∑ j, M i j : ℝ) : ℂ)`. Simplify using `only [Finset.mul_sum, Complex.ofReal_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congrArg (fun t : ℝ => (t : ℂ)) (hrev j i)` as an intermediate fact. Simplify using `only [Complex.ofReal_mul] at this`. Take the linear combination `ω i * this`. Rewrite using `[this, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Combine the equalities or inequalities in the displayed calculation.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ i)]`. Conclude with `mul_le_mul_of_nonneg_left (hM i) (hμ i)`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hμ i)]`.

Conclude with `mul_le_mul_of_nonneg_left (hrow i) (mul_nonneg (hμ i) (norm_nonneg _))`. Use `_ = _ := by rw [Finset.mul_sum, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem kernel_average : KernelAvg := by
  intro ι _ μ M ω e1 e2 hμ hrev hrow hM
  have key : ∑ i, (μ i : ℂ) * ω i = ∑ i, (μ i : ℂ) * ∑ j, (M i j : ℂ) * ω j - ∑ i, (μ i : ℂ) * ω i * (((∑ j, M i j) - 1 : ℝ) : ℂ) := by
    have : ∑ i, (μ i : ℂ) * ∑ j, (M i j : ℂ) * ω j = ∑ i, (μ i : ℂ) * ω i * ((∑ j, M i j : ℝ) : ℂ) := by
      simp only [Finset.mul_sum, Complex.ofReal_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have := congrArg (fun t : ℝ => (t : ℂ)) (hrev j i)
      simp only [Complex.ofReal_mul] at this
      linear_combination ω i * this
    rw [this, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  rw [key]
  calc _ ≤ ‖∑ i, (μ i : ℂ) * ∑ j, (M i j : ℂ) * ω j‖ + ‖∑ i, (μ i : ℂ) * ω i * (((∑ j, M i j) - 1 : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ ∑ i, μ i * (e2 * ‖ω i‖) + ∑ i, μ i * ‖ω i‖ * e1 := by
        gcongr
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ i)]
          exact mul_le_mul_of_nonneg_left (hM i) (hμ i)
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hμ i)]
          exact mul_le_mul_of_nonneg_left (hrow i) (mul_nonneg (hμ i) (norm_nonneg _))
    _ = _ := by rw [Finset.mul_sum, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Introduce `E _ _ V _ _ h O abelian₂ x x' u y v y' m' s c hI hu hm h1 h2`. Use `⟨fun he => ?_, ?_⟩` and prove the remaining obligations. Establish `e : h v u = h m' u`. Use `congrArg (fun z => h z u) he` as an intermediate fact. Simplify `this` using `[h1, h2]`.

Conclude with `⟨e, e ▸ hI _ hm _ hu⟩`. Establish `l : ∀ a b : V, eich h x u s (eich h x' u s (a + c • b)) = eich h x u s (eich h x' u s a) + c • eich h x u s (eich h x' u s b)`. Introduce `a b`. Use `((eichLin h x u s).comp (eichLin h x' u s)).map_add a (c • b)` as an intermediate fact. Rewrite `this` using `[((eichLin h x u s).comp (eichLin h x' u s)).map_smul]`.

Conclude with `this`. Rewrite using `[l]`. Use `module`.
-/
theorem leakage_back_map : LeakBack := by
  intro E _ _ V _ _ h O abelian₂ x x' u y v y' m' s c hI hu hm h1 h2
  refine ⟨fun he => ?_, ?_⟩
  · have e : h v u = h m' u := by
      have := congrArg (fun z => h z u) he
      simpa [h1, h2] using this
    exact ⟨e, e ▸ hI _ hm _ hu⟩
  · have l : ∀ a b : V, eich h x u s (eich h x' u s (a + c • b)) = eich h x u s (eich h x' u s a) + c • eich h x u s (eich h x' u s b) := by
      intro a b
      have := ((eichLin h x u s).comp (eichLin h x' u s)).map_add a (c • b)
      rw [((eichLin h x u s).comp (eichLin h x' u s)).map_smul] at this
      exact this
    rw [l]; module

/- English proof (translation)
Introduce `E _ O th ka n c d hd h1 hk`. Use `choose t ht hkt using hk`. Use `⟨∑ i, d i * t i, O.sum_mem fun i _ => O.mul_mem (hd i) (ht i), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem primitive_cancellation : PrimCancel := by
  intro E _ O th ka n c d hd h1 hk
  choose t ht hkt using hk
  refine ⟨∑ i, d i * t i, O.sum_mem fun i _ => O.mul_mem (hd i) (ht i), ?_⟩
  calc ka = ka * ∑ i, d i * c i := by rw [h1, mul_one]
    _ = ∑ i, d i * (ka * c i) := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [hkt i]; ring

/- English proof (translation)
Introduce `D _ w μ amp ε Mx hw hμ hε ha hM`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun d _ => ?_` and prove the remaining obligations. Establish `h1 : ‖amp d‖ ^ 2 ≤ (ε * μ d) ^ 2` using `by gcongr; exact ha d`. Establish `h2 : (ε * μ d) ^ 2 ≤ ε ^ 2 * Mx * μ d`.

Establish `: μ d * μ d ≤ Mx * μ d` using `mul_le_mul_of_nonneg_right (hM d) (hμ d)`. Use polynomial arithmetic with `[sq_nonneg ε]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem maximal_sum_bound : MaxSum := by
  intro D _ w μ amp ε Mx hw hμ hε ha hM
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  have h1 : ‖amp d‖ ^ 2 ≤ (ε * μ d) ^ 2 := by gcongr; exact ha d
  have h2 : (ε * μ d) ^ 2 ≤ ε ^ 2 * Mx * μ d := by
    have : μ d * μ d ≤ Mx * μ d := mul_le_mul_of_nonneg_right (hM d) (hμ d)
    nlinarith [sq_nonneg ε]
  calc w d * ‖amp d‖ ^ 2 ≤ w d * (ε ^ 2 * Mx * μ d) := mul_le_mul_of_nonneg_left (h1.trans h2) (hw d)
    _ = _ := by ring

/- English proof (translation)
Introduce `R _ n A B hA hA1 hB hB1 j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_add_of_mem j.castSucc j.succ (Finset.mem_univ _) (Finset.mem_univ _)]`. Rewrite using `[hA1, hB1]`. Expand and normalize the polynomial expressions, which then agree. Introduce `hh`.

Use `congrArg Fin.val hh` as an intermediate fact. Simplify using `at this`. Introduce `k _ ⟨h1, h2⟩`. Distinguish the cases in `hk : k < j.castSucc`. Rewrite using `[hA _ _ hk, zero_mul]`.

Establish `: j.succ < k`. Rewrite `hk`, the goal using `[Fin.lt_def]`. Establish `a1 : k.val ≠ j.val` using `fun e => h1 (Fin.ext (by simpa using e))`. Establish `a2 : k.val ≠ j.val + 1` using `fun e => h2 (Fin.ext (by simpa using e))`. Simplify using `at hk ⊢`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hB _ _ this, mul_zero]`.
-/
theorem superdiagonal_addition_invariance : SuperDiagAdd := by
  intro R _ n A B hA hA1 hB hB1 j
  rw [Matrix.mul_apply, Finset.sum_eq_add_of_mem j.castSucc j.succ (Finset.mem_univ _) (Finset.mem_univ _)]
  · rw [hA1, hB1]; ring
  · intro hh; have := congrArg Fin.val hh; simp at this
  · intro k _ ⟨h1, h2⟩
    by_cases hk : k < j.castSucc
    · rw [hA _ _ hk, zero_mul]
    · have : j.succ < k := by
        rw [Fin.lt_def] at hk ⊢
        have a1 : k.val ≠ j.val := fun e => h1 (Fin.ext (by simpa using e))
        have a2 : k.val ≠ j.val + 1 := fun e => h2 (Fin.ext (by simpa using e))
        simp at hk ⊢; omega
      rw [hB _ _ this, mul_zero]

/- English proof (translation)
Introduce `E _ _ V _ _ h O abelian₂ th r f f' g c c' hL hI hg hd hf hc' ⟨w, hw, he⟩ j`. Use `choose t ht hte using hf`. Establish `key : ∑ i, (c' i - c i) • f i = th • (w - ∑ i, c' i • t i)`. Establish `: ∑ i, (c' i - c i) • f i = (∑ i, c' i • f' i - ∑ i, c i • f i) - ∑ i, c' i • (f' i - f i)`. Simplify using `only [sub_smul, smul_sub, Finset.sum_sub_distrib]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this, he, smul_sub, Finset.smul_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hte i, smul_comm]`. Establish `hm : w - ∑ i, c' i • t i ∈ abelian₂` using `abelian₂.sub_mem hw (abelian₂.sum_mem fun i _ => hL _ (hc' i) _ (ht i))`.

Use `⟨h (w - ∑ i, c' i • t i) (g j), hI _ hm _ (hg j), ?_⟩` and prove the remaining obligations. Use `congrArg (fun z => h z (g j)) key` as an intermediate fact. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hd, smul_eq_mul] at this`. Simplify using `using this`.
-/
theorem involution_well_defined : TauWell := by
  intro E _ _ V _ _ h O abelian₂ th r f f' g c c' hL hI hg hd hf hc' ⟨w, hw, he⟩ j
  choose t ht hte using hf
  have key : ∑ i, (c' i - c i) • f i = th • (w - ∑ i, c' i • t i) := by
    have : ∑ i, (c' i - c i) • f i = (∑ i, c' i • f' i - ∑ i, c i • f i) - ∑ i, c' i • (f' i - f i) := by
      simp only [sub_smul, smul_sub, Finset.sum_sub_distrib]; abel
    rw [this, he, smul_sub, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hte i, smul_comm]
  have hm : w - ∑ i, c' i • t i ∈ abelian₂ := abelian₂.sub_mem hw (abelian₂.sum_mem fun i _ => hL _ (hc' i) _ (ht i))
  refine ⟨h (w - ∑ i, c' i • t i) (g j), hI _ hm _ (hg j), ?_⟩
  have := congrArg (fun z => h z (g j)) key
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hd, smul_eq_mul] at this
  simpa using this

/- English proof (translation)
Introduce `P Om H hH`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem orbit_count_formula : OmCount := by
  intro P Om H hH
  calc (2:ℝ)^Om.card = ∏ p ∈ Om, (2:ℝ) := by simp
    _ ≤ ∏ p ∈ Om, H p := Finset.prod_le_prod (fun _ _ => by norm_num) hH

/- English proof (translation)
Introduce `U₀ U₁ _ _ φ₀ φ₁ h`. Rewrite using `[Fintype.sum_prod_type]`. Repeatedly rewrite using `[← Finset.mul_sum]`. Rewrite using `[← Finset.sum_mul, norm_mul]`. Use `gcongr`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem gauss_summand_formula : GaussSummand := by
  intro U₀ U₁ _ _ φ₀ φ₁ h
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, norm_mul]
  gcongr
  calc ‖∑ u, φ₁ u‖ ≤ ∑ u, ‖φ₁ u‖ := norm_sum_le _ _
    _ ≤ ∑ u : U₁, (1:ℝ) := Finset.sum_le_sum (fun u _ => h u)
    _ = _ := by simp

/- English proof (translation)
Introduce `O I _ _ _ _ n`. Establish `e : ((Fin n → O) →ₗ[O] I) ≃ (Fin n → I)` using `((Pi.basisFun O (Fin n)).constr O).symm.toEquiv`. Rewrite using `[Nat.card_congr e, Nat.card_fun]`. Simplify using the standard rewrite rules.
-/
theorem homomorphism_count : HomCount := by
  intro O I _ _ _ _ n
  have e : ((Fin n → O) →ₗ[O] I) ≃ (Fin n → I) := ((Pi.basisFun O (Fin n)).constr O).symm.toEquiv
  rw [Nat.card_congr e, Nat.card_fun]; simp

/- English proof (translation)
Introduce `O A _ _ _ _ m h`. Establish `hs : Function.Surjective (fun s : Fin m → A => Submodule.span O (Set.range s))` using `fun N => h N`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem overlattice_count_formula : OverlatticeCount := by
  intro O A _ _ _ _ m h
  have hs : Function.Surjective (fun s : Fin m → A => Submodule.span O (Set.range s)) := fun N => h N
  calc Nat.card (Submodule O A) ≤ Nat.card (Fin m → A) := Nat.card_le_card_of_surjective _ hs
    _ = _ := by rw [Nat.card_fun]; simp

/- English proof (translation)
Introduce `ι _ V _ v W hW`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => (inv_pos.2 (hW i)).le) (fun i _ => mul_nonneg (hW i).le (sq_nonneg _)) (fun i _ => ?_)` and prove the remaining obligations. Use `(hW i).ne'` as an intermediate fact. Apply `le_of_eq` to reduce the goal to its premises.

Clear the denominators using the available nonvanishing facts.
-/
theorem weighted_cauchy_schwarz : WeightedCS := by
  intro ι _ V _ v W hW
  calc ‖∑ i, v i‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 := by gcongr; exact norm_sum_le _ _
    _ ≤ _ := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => (inv_pos.2 (hW i)).le)
        (fun i _ => mul_nonneg (hW i).le (sq_nonneg _)) (fun i _ => ?_)
      have := (hW i).ne'
      apply le_of_eq
      field_simp

/- English proof (translation)
Introduce `D Ty _ _ w amp hw`. Rewrite using `[Finset.sum_comm, Finset.mul_sum]`. Use `Finset.sum_le_sum fun d _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, mul_left_comm]`. Use `mul_le_mul_of_nonneg_left ?_ (hw d)` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Use `sq_sum_le_card_mul_sum_sq (s := (univ : Finset Ty)) (f := fun t => ‖amp t d‖)` as an intermediate fact. Simplify using `using this`.
-/
theorem type_cauchy_schwarz : TypeCS := by
  intro D Ty _ _ w amp hw
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [← Finset.mul_sum, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (hw d)
  calc ‖∑ t, amp t d‖ ^ 2 ≤ (∑ t, ‖amp t d‖) ^ 2 := by gcongr; exact norm_sum_le _ _
    _ ≤ _ := by
      have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset Ty)) (f := fun t => ‖amp t d‖)
      simpa using this

/- English proof (translation)
Introduce `ι μ M ω e1 e2 hμ hμs hM hMs hrev hω hrow hker`. Take `⟨R, hR⟩ : ∃ R : ι → ℝ, ∀ i, R i = ∑' j, M i j` from `⟨_, fun _ => rfl⟩`. Simplify using `only [← hR] at hrow`. Establish `hRle : ∀ i, R i ≤ 1 + e1` using `fun i => by have := abs_le.1 (hrow i); linarith [this.2]`. Establish `hR0 : ∀ i, 0 ≤ R i` using `fun i => by rw [hR]; exact tsum_nonneg (hM i)`.

Establish `hμR : Summable fun i => μ i * R i` using `Summable.of_nonneg_of_le (fun i => mul_nonneg (hμ i) (hR0 i)) (fun i => mul_le_mul_of_nonneg_left (hRle i) (hμ i)) (hμs.mul_right (1 + e1))`. Establish `hS : Summable (fun p : ι × ι => μ p.1 * M p.1 p.2)`. Rewrite using `[summable_prod_of_nonneg (fun p => mul_nonneg (hμ _) (hM _ _))]`. Use `⟨fun i => (hMs i).mul_left (μ i), ?_⟩` and prove the remaining obligations. Establish `: (fun i => ∑' j, μ i * M i j) = fun i => μ i * R i`.

Use extensionality with `i`. Rewrite using `[hR]`. Conclude with `tsum_mul_left`. Simplify `hμR` using `only [this]`. Establish `hF : Summable (Function.uncurry fun i j => ((μ i * M i j : ℝ) : ℂ) * ω j)`.

Apply `Summable.of_norm` to reduce the goal to its premises. Use `hS.congr ?_` and prove the remaining obligations. Introduce and unpack `⟨i, j⟩`. Simplify using `only [Function.uncurry, norm_mul, hω, mul_one, Complex.norm_real, Real.norm_eq_abs]`. Rewrite using `[← abs_mul, abs_of_nonneg (mul_nonneg (hμ _) (hM _ _))]`.

Establish `hA : ∑' i, (μ i : ℂ) * ∑' j, (M i j : ℂ) * ω j = ∑' i, ((μ i * R i : ℝ) : ℂ) * ω i`. Combine the equalities or inequalities in the displayed calculation. Use `tsum_congr fun i => ?_` and prove the remaining obligations. Rewrite using `[← tsum_mul_left]`. Use `tsum_congr fun j => ?_` and prove the remaining obligations.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑' j, ∑' i, ((μ i * M i j : ℝ) : ℂ) * ω j := (hF.tsum_comm).symm`. Use `_ = _ := by`. Use `tsum_congr fun j => ?_` and prove the remaining obligations.

Rewrite using `[tsum_mul_right]`. Use `congr 1`. Rewrite using `[← Complex.ofReal_tsum]`. Use `congr 1`. Rewrite using `[hR, ← tsum_mul_left]`.

Conclude with `tsum_congr fun i => hrev i j`. Establish `s1 : Summable fun i => ((μ i * R i : ℝ) : ℂ) * ω i`. Apply `Summable.of_norm` to reduce the goal to its premises. Use `hμR.congr fun i => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, hω, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hμ _) (hR0 _))]`.

Establish `s2 : Summable fun i => (μ i : ℂ) * ω i`. Apply `Summable.of_norm` to reduce the goal to its premises. Use `hμs.congr fun i => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, hω, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ _)]`. Establish `key : ∑' i, (μ i : ℂ) * ω i = ∑' i, (μ i : ℂ) * ∑' j, (M i j : ℂ) * ω j - ∑' i, (μ i : ℂ) * ω i * ((R i - 1 : ℝ) : ℂ)`.

Establish `s3 : Summable fun i => (μ i : ℂ) * ω i * ((R i - 1 : ℝ) : ℂ)`. Use `(s1.sub s2).congr fun i => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hA, ← (s1.tsum_sub s3)]`.

Use `tsum_congr fun i => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Establish `b1 : ‖∑' i, (μ i : ℂ) * ∑' j, (M i j : ℂ) * ω j‖ ≤ (∑' i, μ i) * e2`.

Use `tsum_of_norm_bounded (hμs.hasSum.mul_right e2) fun i => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ _)]`. Conclude with `mul_le_mul_of_nonneg_left (hker i) (hμ i)`. Establish `b2 : ‖∑' i, (μ i : ℂ) * ω i * ((R i - 1 : ℝ) : ℂ)‖ ≤ (∑' i, μ i) * e1`. Use `tsum_of_norm_bounded (hμs.hasSum.mul_right e1) fun i => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_mul, hω, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hμ _)]`. Conclude with `mul_le_mul_of_nonneg_left (hrow i) (hμ i)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem kernel_average_sum : KernelAvgSum := by
  intro ι μ M ω e1 e2 hμ hμs hM hMs hrev hω hrow hker
  obtain ⟨R, hR⟩ : ∃ R : ι → ℝ, ∀ i, R i = ∑' j, M i j := ⟨_, fun _ => rfl⟩
  simp only [← hR] at hrow
  have hRle : ∀ i, R i ≤ 1 + e1 := fun i => by have := abs_le.1 (hrow i); linarith [this.2]
  have hR0 : ∀ i, 0 ≤ R i := fun i => by rw [hR]; exact tsum_nonneg (hM i)
  have hμR : Summable fun i => μ i * R i :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hμ i) (hR0 i))
      (fun i => mul_le_mul_of_nonneg_left (hRle i) (hμ i)) (hμs.mul_right (1 + e1))
  have hS : Summable (fun p : ι × ι => μ p.1 * M p.1 p.2) := by
    rw [summable_prod_of_nonneg (fun p => mul_nonneg (hμ _) (hM _ _))]
    refine ⟨fun i => (hMs i).mul_left (μ i), ?_⟩
    have : (fun i => ∑' j, μ i * M i j) = fun i => μ i * R i := by
      ext i; rw [hR]; exact tsum_mul_left
    simpa only [this] using hμR
  have hF : Summable (Function.uncurry fun i j => ((μ i * M i j : ℝ) : ℂ) * ω j) := by
    apply Summable.of_norm
    refine hS.congr ?_
    rintro ⟨i, j⟩
    simp only [Function.uncurry, norm_mul, hω, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [← abs_mul, abs_of_nonneg (mul_nonneg (hμ _) (hM _ _))]
  have hA : ∑' i, (μ i : ℂ) * ∑' j, (M i j : ℂ) * ω j = ∑' i, ((μ i * R i : ℝ) : ℂ) * ω i := by
    calc ∑' i, (μ i : ℂ) * ∑' j, (M i j : ℂ) * ω j
        = ∑' i, ∑' j, ((μ i * M i j : ℝ) : ℂ) * ω j := by
          refine tsum_congr fun i => ?_
          rw [← tsum_mul_left]
          refine tsum_congr fun j => ?_
          push_cast; ring
      _ = ∑' j, ∑' i, ((μ i * M i j : ℝ) : ℂ) * ω j := (hF.tsum_comm).symm
      _ = _ := by
          refine tsum_congr fun j => ?_
          rw [tsum_mul_right]
          congr 1
          rw [← Complex.ofReal_tsum]
          congr 1
          rw [hR, ← tsum_mul_left]
          exact tsum_congr fun i => hrev i j
  have s1 : Summable fun i => ((μ i * R i : ℝ) : ℂ) * ω i := by
    apply Summable.of_norm
    refine hμR.congr fun i => ?_
    rw [norm_mul, hω, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hμ _) (hR0 _))]
  have s2 : Summable fun i => (μ i : ℂ) * ω i := by
    apply Summable.of_norm
    refine hμs.congr fun i => ?_
    rw [norm_mul, hω, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ _)]
  have key : ∑' i, (μ i : ℂ) * ω i
      = ∑' i, (μ i : ℂ) * ∑' j, (M i j : ℂ) * ω j - ∑' i, (μ i : ℂ) * ω i * ((R i - 1 : ℝ) : ℂ) := by
    have s3 : Summable fun i => (μ i : ℂ) * ω i * ((R i - 1 : ℝ) : ℂ) := by
      refine (s1.sub s2).congr fun i => ?_
      push_cast; ring
    rw [hA, ← (s1.tsum_sub s3)]
    refine tsum_congr fun i => ?_
    push_cast; ring
  rw [key]
  have b1 : ‖∑' i, (μ i : ℂ) * ∑' j, (M i j : ℂ) * ω j‖ ≤ (∑' i, μ i) * e2 := by
    refine tsum_of_norm_bounded (hμs.hasSum.mul_right e2) fun i => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ _)]
    exact mul_le_mul_of_nonneg_left (hker i) (hμ i)
  have b2 : ‖∑' i, (μ i : ℂ) * ω i * ((R i - 1 : ℝ) : ℂ)‖ ≤ (∑' i, μ i) * e1 := by
    refine tsum_of_norm_bounded (hμs.hasSum.mul_right e1) fun i => ?_
    rw [norm_mul, norm_mul, hω, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (hμ _)]
    exact mul_le_mul_of_nonneg_left (hrow i) (hμ i)
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ (∑' i, μ i) * e2 + (∑' i, μ i) * e1 := add_le_add b1 b2
    _ = _ := by ring

/- English proof (translation)
Introduce `c C₀`. Choose the witnesses or unpack the hypotheses as in `⟨C', hC'⟩ : ∃ n : ℕ, max 1 (C₀ ^ 2) ≤ (2 : ℝ) ^ n := by`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (max 1 (C₀ ^ 2)) (by norm_num : (1 : ℝ) < 2)`. Conclude with `⟨n, hn.le⟩`. Use `⟨4 * c + C', ?_⟩` and prove the remaining obligations.

Introduce `k r q e H nn D Ty _ _ w amp μ be I isBe he hk hq hH hqH hnn hw hTy hbe hI hIbe hIal hμ hμM hsum hamp hampbe`. Take `⟨K, rfl⟩ : ∃ K, k = K + 2 * r + 5` from `⟨k - 2 * r - 5, by omega⟩`. Establish `hq0 : (0 : ℝ) < q` using `by positivity`. Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast (by omega : 1 ≤ q)`. Establish `e1 : (q : ℝ) ^ (-(((K + 2 * r + 5 : ℕ) : ℤ) - 2 * r - 5)) = ((q : ℝ) ^ K)⁻¹`.

Rewrite using `[← zpow_natCast, ← zpow_neg]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (q : ℝ) ^ (1 - (((K + 2 * r + 5 : ℕ) : ℤ) - 2 * r - 3)) = ((q : ℝ) ^ (K + 1))⁻¹`.

Rewrite using `[← zpow_natCast, ← zpow_neg]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`.

Rewrite `hampbe` using `[e2]`. Establish `e3 : K + 2 * r + 5 - 1 = K + (2 * r + 4)` using `by omega`. Rewrite `hμM`, `hsum` using `[e3]`. Use `set B : ℝ := max 1 (C₀ ^ 2) with hB`. Establish `hB1 : 1 ≤ B` using `le_max_left _ _`.

Establish `hHc : 0 < H ^ (c * e)` using `by positivity`. Distinguish the cases in `hne : Nonempty Ty`. Use `swap`. Establish `: IsEmpty Ty` using `not_nonempty_iff.1 hne`. Simplify using `only [Finset.univ_eq_empty, Finset.sum_empty, norm_zero]`.

Simplify using `only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero]`. Check the signs of the components of the expression. Establish `hqH'` using `hqH hne`. Establish `per : ∀ t, ∑ d, w d * ‖amp t d‖ ^ 2 ≤ B * H ^ (c * e) * H ^ (c * e) * ((q : ℝ) ^ K)⁻¹ * nn`. Introduce `t`.

Establish `hbe0 : 0 < be t` using `lt_of_lt_of_le one_pos (hbe t)`. Choose the witnesses or unpack the hypotheses as in `⟨ε, hε0, hε, hεb⟩ : ∃ ε : ℝ, 0 ≤ ε ∧ (∀ d, ‖amp t d‖ ≤ ε * μ t d) ∧ ε ^ 2 * (I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹) ≤ B * ((q : ℝ) ^ K)⁻¹ := by`. Distinguish the cases in `hb : isBe t`. Use `⟨|C₀| * ((q : ℝ) ^ (K + 1))⁻¹, by positivity, fun d => ?_, ?_⟩` and prove the remaining obligations. Use `(hampbe t d hb).trans ?_ gcongr` and prove the remaining obligations.

Conclude with `hμ t d`. Conclude with `le_abs_self _`. Establish `h1 : I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹ ≤ 1`. Rewrite using `[← div_eq_mul_inv, div_le_one (by positivity)]`. Conclude with `pow_le_pow_left₀ (hI t) (hIbe t) _`.

Establish `h2 : (|C₀| * ((q : ℝ) ^ (K + 1))⁻¹) ^ 2 ≤ B * ((q : ℝ) ^ K)⁻¹`. Rewrite using `[mul_pow, sq_abs]`. Establish `h3 : (((q : ℝ) ^ (K + 1))⁻¹) ^ 2 ≤ ((q : ℝ) ^ K)⁻¹`. Rewrite using `[inv_pow, ← pow_mul]`. Apply `inv_anti₀ (by positivity)` to reduce the goal to its premises.

Conclude with `pow_le_pow_right₀ hq1 (by omega)`. Conclude with `mul_le_mul (le_max_right _ _) h3 (by positivity) (by positivity)`. Combine the equalities or inequalities in the displayed calculation. Use `⟨1, zero_le_one, fun d => by rw [one_mul]; exact hamp t d, ?_⟩` and prove the remaining obligations. Establish `h1 : I t ^ (K + (2 * r + 4)) ≤ be t ^ (K + (2 * r + 4)) * ((q : ℝ) ^ (K + (2 * r + 4)))⁻¹`.

Rewrite using `[← div_eq_mul_inv, ← div_pow]`. Conclude with `pow_le_pow_left₀ (hI t) (hIal t hb) _`. Establish `h2 : I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹ ≤ ((q : ℝ) ^ (K + (2 * r + 4)))⁻¹`. Rewrite using `[← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith [h1]`. Establish `h3 : ((q : ℝ) ^ (K + (2 * r + 4)))⁻¹ ≤ ((q : ℝ) ^ K)⁻¹`.

Apply `inv_anti₀ (by positivity)` to reduce the goal to its premises. Conclude with `pow_le_pow_right₀ hq1 (by omega)`. Combine the equalities or inequalities in the displayed calculation. Establish `hms` using `maximal_sum_bound D w (μ t) (amp t) ε (H ^ (c * e) * I t ^ (K + (2 * r + 4))) hw (hμ t) hε0 hε (hμM t)`. Establish `hI' : 0 ≤ I t ^ (K + (2 * r + 4))` using `pow_nonneg (hI t) _`.

Combine the equalities or inequalities in the displayed calculation. Establish `hBH : B ≤ H ^ (C' * e)`. Combine the equalities or inequalities in the displayed calculation. Use `le_trans ?_ hqH'` and prove the remaining obligations. Conclude with `hq` after adjusting the coercions.

Use `_ ≤ H ^ (C' * e) := pow_le_pow_right₀ hH (Nat.le_mul_of_pos_right _ he)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun d _ => mul_nonneg (hw d) (sq_nonneg _)`. Conclude with `per t`. Use `_ = (Fintype.card Ty : ℝ) * (H ^ (c * e) * (B * H ^ (c * e) * H ^ (c * e) * ((q : ℝ) ^ K)⁻¹ * nn)) := by`.

Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ H ^ (c * e) * (H ^ (c * e) * (H ^ (C' * e) * H ^ (c * e) * H ^ (c * e) * ((q : ℝ) ^ K)⁻¹ * nn)) := by gcongr`. Use `_ = _ := by`. Establish `: H ^ ((4 * c + C') * e) = H ^ (c * e) * H ^ (c * e) * H ^ (c * e) * H ^ (c * e) * H ^ (C' * e)`.

Rewrite using `[← pow_add, ← pow_add, ← pow_add, ← pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermitian_count_assembly : AssemblyNG := by
  intro c C₀
  obtain ⟨C', hC'⟩ : ∃ n : ℕ, max 1 (C₀ ^ 2) ≤ (2 : ℝ) ^ n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max 1 (C₀ ^ 2)) (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, hn.le⟩
  refine ⟨4 * c + C', ?_⟩
  intro k r q e H nn D Ty _ _ w amp μ be I isBe he hk hq hH hqH hnn hw hTy hbe hI hIbe hIal hμ hμM hsum hamp hampbe
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 2 * r + 5 := ⟨k - 2 * r - 5, by omega⟩
  have hq0 : (0 : ℝ) < q := by positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have e1 : (q : ℝ) ^ (-(((K + 2 * r + 5 : ℕ) : ℤ) - 2 * r - 5)) = ((q : ℝ) ^ K)⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
  have e2 : (q : ℝ) ^ (1 - (((K + 2 * r + 5 : ℕ) : ℤ) - 2 * r - 3)) = ((q : ℝ) ^ (K + 1))⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
  rw [e1]; rw [e2] at hampbe
  have e3 : K + 2 * r + 5 - 1 = K + (2 * r + 4) := by omega
  rw [e3] at hμM hsum
  set B : ℝ := max 1 (C₀ ^ 2) with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  have hHc : 0 < H ^ (c * e) := by positivity
  by_cases hne : Nonempty Ty
  swap
  · have : IsEmpty Ty := not_nonempty_iff.1 hne
    simp only [Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero]
    positivity
  have hqH' := hqH hne
  have per : ∀ t, ∑ d, w d * ‖amp t d‖ ^ 2 ≤ B * H ^ (c * e) * H ^ (c * e) * ((q : ℝ) ^ K)⁻¹ * nn := by
    intro t
    have hbe0 : 0 < be t := lt_of_lt_of_le one_pos (hbe t)
    obtain ⟨ε, hε0, hε, hεb⟩ : ∃ ε : ℝ, 0 ≤ ε ∧ (∀ d, ‖amp t d‖ ≤ ε * μ t d) ∧
        ε ^ 2 * (I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹) ≤ B * ((q : ℝ) ^ K)⁻¹ := by
      by_cases hb : isBe t
      · refine ⟨|C₀| * ((q : ℝ) ^ (K + 1))⁻¹, by positivity, fun d => ?_, ?_⟩
        · refine (hampbe t d hb).trans ?_
          gcongr
          · exact hμ t d
          · exact le_abs_self _
        · have h1 : I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹ ≤ 1 := by
            rw [← div_eq_mul_inv, div_le_one (by positivity)]
            exact pow_le_pow_left₀ (hI t) (hIbe t) _
          have h2 : (|C₀| * ((q : ℝ) ^ (K + 1))⁻¹) ^ 2 ≤ B * ((q : ℝ) ^ K)⁻¹ := by
            rw [mul_pow, sq_abs]
            have h3 : (((q : ℝ) ^ (K + 1))⁻¹) ^ 2 ≤ ((q : ℝ) ^ K)⁻¹ := by
              rw [inv_pow, ← pow_mul]
              apply inv_anti₀ (by positivity)
              exact pow_le_pow_right₀ hq1 (by omega)
            exact mul_le_mul (le_max_right _ _) h3 (by positivity) (by positivity)
          calc _ ≤ (|C₀| * ((q : ℝ) ^ (K + 1))⁻¹) ^ 2 * 1 := by gcongr
            _ ≤ _ := by rw [mul_one]; exact h2
      · refine ⟨1, zero_le_one, fun d => by rw [one_mul]; exact hamp t d, ?_⟩
        have h1 : I t ^ (K + (2 * r + 4)) ≤ be t ^ (K + (2 * r + 4)) * ((q : ℝ) ^ (K + (2 * r + 4)))⁻¹ := by
          rw [← div_eq_mul_inv, ← div_pow]
          exact pow_le_pow_left₀ (hI t) (hIal t hb) _
        have h2 : I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹ ≤ ((q : ℝ) ^ (K + (2 * r + 4)))⁻¹ := by
          rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith [h1]
        have h3 : ((q : ℝ) ^ (K + (2 * r + 4)))⁻¹ ≤ ((q : ℝ) ^ K)⁻¹ := by
          apply inv_anti₀ (by positivity)
          exact pow_le_pow_right₀ hq1 (by omega)
        calc _ = I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹ := by ring
          _ ≤ 1 * ((q : ℝ) ^ K)⁻¹ := by rw [one_mul]; exact h2.trans h3
          _ ≤ _ := by gcongr
    have hms := maximal_sum_bound D w (μ t) (amp t) ε (H ^ (c * e) * I t ^ (K + (2 * r + 4))) hw (hμ t) hε0 hε (hμM t)
    have hI' : 0 ≤ I t ^ (K + (2 * r + 4)) := pow_nonneg (hI t) _
    calc _ ≤ _ := hms
      _ ≤ ε ^ 2 * (H ^ (c * e) * I t ^ (K + (2 * r + 4))) * (H ^ (c * e) * (be t ^ (K + (2 * r + 4)))⁻¹ * nn) := by
          gcongr; exact hsum t
      _ = (ε ^ 2 * (I t ^ (K + (2 * r + 4)) * (be t ^ (K + (2 * r + 4)))⁻¹)) * (H ^ (c * e) * H ^ (c * e) * nn) := by ring
      _ ≤ (B * ((q : ℝ) ^ K)⁻¹) * (H ^ (c * e) * H ^ (c * e) * nn) := by gcongr
      _ = _ := by ring
  have hBH : B ≤ H ^ (C' * e) := by
    calc B ≤ (2 : ℝ) ^ C' := hC'
      _ ≤ H ^ C' := by
          gcongr
          refine le_trans ?_ hqH'
          exact_mod_cast hq
      _ ≤ H ^ (C' * e) := pow_le_pow_right₀ hH (Nat.le_mul_of_pos_right _ he)
  calc _ ≤ _ := type_cauchy_schwarz D Ty w amp hw
    _ ≤ H ^ (c * e) * ∑ t : Ty, B * H ^ (c * e) * H ^ (c * e) * ((q : ℝ) ^ K)⁻¹ * nn := by
        gcongr with t
        · exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun d _ => mul_nonneg (hw d) (sq_nonneg _)
        · exact per t
    _ = (Fintype.card Ty : ℝ) * (H ^ (c * e) * (B * H ^ (c * e) * H ^ (c * e) * ((q : ℝ) ^ K)⁻¹ * nn)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ H ^ (c * e) * (H ^ (c * e) * (H ^ (C' * e) * H ^ (c * e) * H ^ (c * e) * ((q : ℝ) ^ K)⁻¹ * nn)) := by
        gcongr
    _ = _ := by
        have : H ^ ((4 * c + C') * e) = H ^ (c * e) * H ^ (c * e) * H ^ (c * e) * H ^ (c * e) * H ^ (C' * e) := by
          rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
        rw [this]; ring

/- English proof (translation)
Introduce `P _ _ Om D _ w aN aZ H nn ngen q c κ hw hH hq hnn hN hZ hgen`. Use `set 𝒜 := Om.powerset.filter (fun A => A.Nonempty) with h𝒜`. Establish `hcard : (𝒜.card : ℝ) ≤ (2 : ℝ) ^ Om.card`. Establish `: 𝒜.card ≤ 2 ^ Om.card`. Rewrite using `[← Finset.card_powerset]`.

Conclude with `Finset.card_filter_le _ _`. Conclude with `this` after adjusting the coercions. Establish `hHc : ∀ p, 0 < H p ^ c` using `fun p => pow_pos (lt_of_lt_of_le one_pos (hH p)) _`. Establish `one : ∀ A ∈ 𝒜, ∏ p, ∑ x : D p, w p x * ‖(if p ∈ A then aN p x else aZ p x)‖ ^ 2 ≤ (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p`. Introduce `A hA`.

Choose the witnesses or unpack the hypotheses as in `⟨hAO, p0, hp0⟩ : A ⊆ Om ∧ A.Nonempty := by`. Simplify `hA` using `[h𝒜, Finset.mem_filter, Finset.mem_powerset]`. Use `set g : P → ℝ := fun p => if p ∈ A then ((q p : ℝ) ^ κ)⁻¹ else 1 with hg`. Apply the tactic sequence `have hg0 : ∀ p, 0 ≤ g p := fun p => by simp only [hg]; split_ifs <;> positivity`. Establish `hq2 : ∀ p, ((q p : ℝ) ^ κ)⁻¹ ≤ ((2 : ℝ) ^ κ)⁻¹` using `fun p => by`.

Apply `inv_anti₀ (by positivity)` to reduce the goal to its premises. Use `gcongr`. Conclude with `hq p` after adjusting the coercions. Establish `h21 : ((2 : ℝ) ^ κ)⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))`. Establish `hg1 : ∀ p, g p ≤ 1` using `fun p => by`.

Simplify using `only [hg]`. Use `split_ifs`. Conclude with `(hq2 p).trans h21`. Conclude with `le_rfl`. Establish `hgp : ∏ p, g p ≤ ((2 : ℝ) ^ κ)⁻¹`.

Rewrite using `[← Finset.mul_prod_erase univ g (Finset.mem_univ p0)]`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul` to reduce the goal to its premises. Simplify using `only [hg, if_pos hp0]`. Conclude with `hq2 p0`.

Conclude with `Finset.prod_le_one (fun p _ => hg0 p) (fun p _ => hg1 p)`. Conclude with `Finset.prod_nonneg fun p _ => hg0 p`. Check the signs of the components of the expression. Use `_ = _ := mul_one _`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun x _ => mul_nonneg (hw p x) (sq_nonneg _)) fun p _ => ?_` and prove the remaining obligations. Establish `hb : H p ^ c * nn p ≤ H p ^ c * (H p ^ c * ngen p)` using `mul_le_mul_of_nonneg_left (hgen p) (hHc p).le`. Distinguish the cases in `hp : p ∈ A`. Simplify using `only [hg, if_pos hp]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [hg, if_neg hp, mul_one]`. Conclude with `(hZ p).trans hb`. Use `_ = ((∏ p, H p) ^ (2 * c) * ∏ p, ngen p) * ∏ p, g p := by`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, two_mul, pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ ((∏ p, H p) ^ (2 * c) * ∏ p, ngen p) * ((2 : ℝ) ^ κ)⁻¹ := by`. Use `mul_le_mul_of_nonneg_left hgp ?_` and prove the remaining obligations. Use `mul_nonneg (pow_nonneg (Finset.prod_nonneg fun p _ => (zero_le_one.trans (hH p))) _) (Finset.prod_nonneg fun p _ => ?_)` and prove the remaining obligations. Use `(hnn p).trans (hgen p)` as an intermediate fact. Conclude with `nonneg_of_mul_nonneg_right this (hHc p)`.

Use `_ = _ := by ring`. Establish `hR0 : 0 ≤ (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p`. Use `mul_nonneg (mul_nonneg (pow_nonneg (Finset.prod_nonneg fun p _ => (zero_le_one.trans (hH p))) _) (by positivity)) (Finset.prod_nonneg fun p _ => ?_)` and prove the remaining obligations. Use `(hnn p).trans (hgen p)` as an intermediate fact. Conclude with `nonneg_of_mul_nonneg_right this (hHc p)`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun p _ => hw p _)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use `Finset.sum_congr rfl fun A _ => ?_` and prove the remaining obligations.

Rewrite using `[norm_prod, Finset.prod_pow]`. Use `_ = (𝒜.card : ℝ) * ∑ A ∈ 𝒜, ∏ p, ∑ x : D p, w p x * ‖(if p ∈ A then aN p x else aZ p x)‖ ^ 2 := by`. Repeatedly rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (2 : ℝ) ^ Om.card * ∑ A ∈ 𝒜, (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p := by`. Apply `mul_le_mul hcard (Finset.sum_le_sum one) _ (by positivity)` to reduce the goal to its premises. Conclude with `Finset.sum_nonneg fun A _ => Finset.prod_nonneg fun p _ => Finset.sum_nonneg fun x _ => mul_nonneg (hw p x) (sq_nonneg _)`.

Use `_ = (2 : ℝ) ^ Om.card * ((𝒜.card : ℝ) * ((∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p)) := by`. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ (2 : ℝ) ^ Om.card * ((2 : ℝ) ^ Om.card * ((∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p)) := by gcongr`. Use `_ = _ := by`. Establish `: (4 : ℝ) ^ Om.card = (2 : ℝ) ^ Om.card * (2 : ℝ) ^ Om.card`.

Rewrite using `[← mul_pow]`. Evaluate the numerical expressions. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fourth_reduction_identity : Step4 := by
  intro P _ _ Om D _ w aN aZ H nn ngen q c κ hw hH hq hnn hN hZ hgen
  set 𝒜 := Om.powerset.filter (fun A => A.Nonempty) with h𝒜
  have hcard : (𝒜.card : ℝ) ≤ (2 : ℝ) ^ Om.card := by
    have : 𝒜.card ≤ 2 ^ Om.card := by
      rw [← Finset.card_powerset]; exact Finset.card_filter_le _ _
    exact_mod_cast this
  have hHc : ∀ p, 0 < H p ^ c := fun p => pow_pos (lt_of_lt_of_le one_pos (hH p)) _

  have one : ∀ A ∈ 𝒜, ∏ p, ∑ x : D p, w p x * ‖(if p ∈ A then aN p x else aZ p x)‖ ^ 2
      ≤ (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p := by
    intro A hA
    obtain ⟨hAO, p0, hp0⟩ : A ⊆ Om ∧ A.Nonempty := by
      simpa [h𝒜, Finset.mem_filter, Finset.mem_powerset] using hA
    set g : P → ℝ := fun p => if p ∈ A then ((q p : ℝ) ^ κ)⁻¹ else 1 with hg
    have hg0 : ∀ p, 0 ≤ g p := fun p => by simp only [hg]; split_ifs <;> positivity
    have hq2 : ∀ p, ((q p : ℝ) ^ κ)⁻¹ ≤ ((2 : ℝ) ^ κ)⁻¹ := fun p => by
      apply inv_anti₀ (by positivity)
      gcongr
      exact_mod_cast hq p
    have h21 : ((2 : ℝ) ^ κ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hg1 : ∀ p, g p ≤ 1 := fun p => by
      simp only [hg]; split_ifs
      · exact (hq2 p).trans h21
      · exact le_rfl
    have hgp : ∏ p, g p ≤ ((2 : ℝ) ^ κ)⁻¹ := by
      rw [← Finset.mul_prod_erase univ g (Finset.mem_univ p0)]
      calc g p0 * ∏ p ∈ univ.erase p0, g p ≤ ((2 : ℝ) ^ κ)⁻¹ * 1 := by
            apply mul_le_mul
            · simp only [hg, if_pos hp0]; exact hq2 p0
            · exact Finset.prod_le_one (fun p _ => hg0 p) (fun p _ => hg1 p)
            · exact Finset.prod_nonneg fun p _ => hg0 p
            · positivity
        _ = _ := mul_one _
    calc ∏ p, ∑ x : D p, w p x * ‖(if p ∈ A then aN p x else aZ p x)‖ ^ 2
        ≤ ∏ p, (H p ^ c * (H p ^ c * ngen p)) * g p := by
          refine Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun x _ => mul_nonneg (hw p x) (sq_nonneg _))
            fun p _ => ?_
          have hb : H p ^ c * nn p ≤ H p ^ c * (H p ^ c * ngen p) :=
            mul_le_mul_of_nonneg_left (hgen p) (hHc p).le
          by_cases hp : p ∈ A
          · simp only [hg, if_pos hp]
            calc _ ≤ _ := hN p (hAO hp)
              _ = (H p ^ c * nn p) * ((q p : ℝ) ^ κ)⁻¹ := by ring
              _ ≤ _ := by gcongr
          · simp only [hg, if_neg hp, mul_one]
            exact (hZ p).trans hb
      _ = ((∏ p, H p) ^ (2 * c) * ∏ p, ngen p) * ∏ p, g p := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
            Finset.prod_pow, two_mul, pow_add]; ring
      _ ≤ ((∏ p, H p) ^ (2 * c) * ∏ p, ngen p) * ((2 : ℝ) ^ κ)⁻¹ := by
          refine mul_le_mul_of_nonneg_left hgp ?_
          refine mul_nonneg (pow_nonneg (Finset.prod_nonneg fun p _ => (zero_le_one.trans (hH p))) _)
            (Finset.prod_nonneg fun p _ => ?_)
          have := (hnn p).trans (hgen p)
          exact nonneg_of_mul_nonneg_right this (hHc p)
      _ = _ := by ring
  have hR0 : 0 ≤ (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p := by
    refine mul_nonneg (mul_nonneg (pow_nonneg (Finset.prod_nonneg fun p _ => (zero_le_one.trans (hH p))) _) (by positivity))
      (Finset.prod_nonneg fun p _ => ?_)
    have := (hnn p).trans (hgen p)
    exact nonneg_of_mul_nonneg_right this (hHc p)
  calc ∑ d : (∀ p, D p), (∏ p, w p (d p)) *
        ‖∑ A ∈ 𝒜, ∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2
      ≤ ∑ d : (∀ p, D p), (∏ p, w p (d p)) *
          ((𝒜.card : ℝ) * ∑ A ∈ 𝒜, ∏ p, ‖(if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2) := by
        refine Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun p _ => hw p _)
        calc ‖∑ A ∈ 𝒜, ∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2
            ≤ (∑ A ∈ 𝒜, ‖∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖) ^ 2 := by
              gcongr; exact norm_sum_le _ _
          _ ≤ (𝒜.card : ℝ) * ∑ A ∈ 𝒜, ‖∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2 :=
              sq_sum_le_card_mul_sum_sq
          _ = _ := by
              congr 1
              refine Finset.sum_congr rfl fun A _ => ?_
              rw [norm_prod, Finset.prod_pow]
    _ = (𝒜.card : ℝ) * ∑ A ∈ 𝒜, ∏ p, ∑ x : D p, w p x * ‖(if p ∈ A then aN p x else aZ p x)‖ ^ 2 := by
        simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    _ ≤ (2 : ℝ) ^ Om.card * ∑ A ∈ 𝒜, (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p := by
        apply mul_le_mul hcard (Finset.sum_le_sum one) _ (by positivity)
        exact Finset.sum_nonneg fun A _ => Finset.prod_nonneg fun p _ => Finset.sum_nonneg fun x _ =>
          mul_nonneg (hw p x) (sq_nonneg _)
    _ = (2 : ℝ) ^ Om.card * ((𝒜.card : ℝ) * ((∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ Om.card * ((2 : ℝ) ^ Om.card * ((∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p)) := by
        gcongr
    _ = _ := by
        have : (4 : ℝ) ^ Om.card = (2 : ℝ) ^ Om.card * (2 : ℝ) ^ Om.card := by
          rw [← mul_pow]; norm_num
        rw [this]; ring

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ N ih`. Rewrite using `[Finset.sum_range_succ, pow_succ]`. Establish `: 0 ≤ y ^ N` using `pow_nonneg hy0 _`.

Use the polynomial consequences of the given equalities and inequalities.
-/
lemma geo_half (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) (N : ℕ) : ∑ l ∈ range N, y ^ l ≤ 2 - 2 * y ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have : 0 ≤ y ^ N := pow_nonneg hy0 _
    nlinarith

/- English proof (translation)
Use `⟨(univ.sup cond) + 1, fun N' hN' => ?_⟩` and prove the remaining obligations. Establish `hmaps : ∀ ψ ∈ (univ : Finset Ψ), cond ψ ∈ range N'` using `fun ψ _ => by`. Use `Finset.le_sup (f := cond) (Finset.mem_univ ψ)` as an intermediate fact. Rewrite using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[← Finset.sum_fiberwise_of_maps_to hmaps]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Use `le_trans (le_of_eq ?_) (hb i)` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (fun ψ hψ => by rw [(Finset.mem_filter.1 hψ).2] : ∀ ψ ∈ univ.filter (fun ψ => cond ψ = i), g (cond ψ) = g i), Finset.sum_const, nsmul_eq_mul]`.
-/
lemma sum_cond_le {Ψ : Type*} [Fintype Ψ] (cond : Ψ → ℕ) (g B : ℕ → ℝ)
    (hb : ∀ i, ((univ.filter fun ψ => cond ψ = i).card : ℝ) * g i ≤ B i) :
    ∃ N, ∀ N' ≥ N, ∑ ψ, g (cond ψ) ≤ ∑ i ∈ range N', B i := by
  refine ⟨(univ.sup cond) + 1, fun N' hN' => ?_⟩
  have hmaps : ∀ ψ ∈ (univ : Finset Ψ), cond ψ ∈ range N' := fun ψ _ => by
    have := Finset.le_sup (f := cond) (Finset.mem_univ ψ)
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun i _ => ?_
  refine le_trans (le_of_eq ?_) (hb i)
  rw [Finset.sum_congr rfl (fun ψ hψ => by rw [(Finset.mem_filter.1 hψ).2] : ∀ ψ ∈ univ.filter (fun ψ => cond ψ = i), g (cond ψ) = g i),
    Finset.sum_const, nsmul_eq_mul]

/- English proof (translation)
Rewrite using `[Finset.sum_comm, Finset.sum_filter, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul, AddChar.sum_apply_eq_ite]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
lemma orth_sum {U T : Type} [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (f : U → ℂ) :
    (∑ u ∈ univ.filter (fun u => Q u = 0), f u) * (Fintype.card T : ℂ)
      = ∑ ψ : AddChar T ℂ, ∑ u, ψ (Q u) * f u := by
  rw [Finset.sum_comm, Finset.sum_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite]
  split_ifs <;> ring

/- English proof (translation)
Establish `hq0 : (0 : ℝ) < q` using `by positivity`. Establish `hq2 : (2 : ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `h1 : (q : ℝ) ^ (1 - (ρ : ℤ)) = q * ((q : ℝ) ^ ρ)⁻¹`. Rewrite using `[zpow_sub₀ hq0.ne', zpow_one, zpow_natCast, div_eq_mul_inv]`. Use `⟨h1, by positivity, ?_⟩` and prove the remaining obligations.

Take `⟨ρ', rfl⟩ : ∃ ρ', ρ = ρ' + 4` from `⟨ρ - 4, by omega⟩`. Establish `h2 : (q : ℝ) * ((q : ℝ) ^ (ρ' + 4))⁻¹ = ((q : ℝ) ^ (ρ' + 3))⁻¹`. Rewrite using `[pow_succ (q : ℝ) (ρ' + 3)]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h1, h2, one_div]`.

Apply `inv_anti₀ (by norm_num)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
lemma y_facts (q ρ : ℕ) (hq : 2 ≤ q) (hρ : 4 ≤ ρ) :
    (q : ℝ) ^ (1 - (ρ : ℤ)) = q * ((q : ℝ) ^ ρ)⁻¹ ∧ 0 ≤ (q : ℝ) ^ (1 - (ρ : ℤ)) ∧
      (q : ℝ) ^ (1 - (ρ : ℤ)) ≤ 1 / 8 := by
  have hq0 : (0 : ℝ) < q := by positivity
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (q : ℝ) ^ (1 - (ρ : ℤ)) = q * ((q : ℝ) ^ ρ)⁻¹ := by
    rw [zpow_sub₀ hq0.ne', zpow_one, zpow_natCast, div_eq_mul_inv]
  refine ⟨h1, by positivity, ?_⟩
  obtain ⟨ρ', rfl⟩ : ∃ ρ', ρ = ρ' + 4 := ⟨ρ - 4, by omega⟩
  have h2 : (q : ℝ) * ((q : ℝ) ^ (ρ' + 4))⁻¹ = ((q : ℝ) ^ (ρ' + 3))⁻¹ := by
    rw [pow_succ (q : ℝ) (ρ' + 3)]; field_simp
  rw [h1, h2, one_div]
  apply inv_anti₀ (by norm_num)
  calc (8 : ℝ) = 2 ^ 3 := by norm_num
    _ ≤ (q : ℝ) ^ 3 := by gcongr
    _ ≤ (q : ℝ) ^ (ρ' + 3) := pow_le_pow_right₀ (by linarith) (by omega)

/- English proof (translation)
Take `⟨hy, hy0, hy8⟩` from `y_facts q ρ hq hρ`. Use `set y : ℝ := (q : ℝ) ^ (1 - (ρ : ℤ))`. Establish `hq0 : (0 : ℝ) < q` using `by positivity`. Use `set g : ℕ → ℝ := fun i => if i = 0 then 0 else ((q : ℝ) ^ (i * ρ))⁻¹ with hg`. Use `set B : ℕ → ℝ := fun i => if i = 0 then 0 else y ^ i with hB`.

Establish `hgB : ∀ i, ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) * g i ≤ B i`. Introduce `i`. Distinguish the cases in `hi : i = 0`. Simplify using `[hg, hB, hi]`. Simplify using `only [hg, hB, if_neg hi]`.

Establish `: y ^ i = (q : ℝ) ^ i * ((q : ℝ) ^ (i * ρ))⁻¹`. Rewrite using `[hy, mul_pow, inv_pow, ← pow_mul, mul_comm ρ i]`. Rewrite using `[this]`. Use `gcongr`. Conclude with `hcnt i (Nat.one_le_iff_ne_zero.2 hi)`.

Take `⟨N, hN⟩` from `sum_cond_le cond g B hgB`. Establish `hsumB : ∑ i ∈ range (N + 1), B i ≤ 2 * y`. Rewrite using `[Finset.sum_range_succ']`. Simplify using `only [hB, if_true, add_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]`. Use `geo_half y hy0 (by linarith) N` as an intermediate fact.

Establish `h2 : ∑ k ∈ range N, y ^ (k + 1) = y * ∑ k ∈ range N, y ^ k`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring`. Rewrite using `[h2]`. Establish `h3 : 0 ≤ y ^ N` using `pow_nonneg hy0 _`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hmain : ‖(∑ u ∈ univ.filter (fun u => Q u = 0), f u) * ((q : ℂ) ^ a) - ∑ u, f u‖ ≤ 2 * y * (Fintype.card U : ℝ)`. Establish `h0` using `orth_sum Q f`. Rewrite `h0` using `[hT, ← Finset.add_sum_erase univ _ (Finset.mem_univ (0 : AddChar T ℂ))]`. Simplify using `only [AddChar.zero_apply, one_mul] at h0`. Move the coercions through the operations in `at h0`.

Rewrite using `[h0, add_sub_cancel_left]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun ψ hψ => ?_` and prove the remaining obligations. Establish `hψ0 : ψ ≠ 0` using `(Finset.mem_erase.1 hψ).1`. Establish `: cond ψ ≠ 0` using `fun h => hψ0 ((hc0 ψ).1 h)`.

Simplify using `only [hg, if_neg this]`. Conclude with `hS ψ hψ0`. Use `_ ≤ ∑ ψ, g (cond ψ) * (Fintype.card U : ℝ) := by`. Use `Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun ψ _ _ => ?_` and prove the remaining obligations. Apply the tactic sequence `simp only [hg]; split_ifs <;> positivity`.

Use `_ = (∑ ψ, g (cond ψ)) * (Fintype.card U : ℝ) := by rw [Finset.sum_mul]`. Use `_ ≤ _ := by gcongr`. Conclude with `(hN (N + 1) (by omega)).trans hsumB`. Establish `hqa : ((q : ℂ) ^ a) ≠ 0`. Establish `: (q : ℂ) ≠ 0` using `by exact_mod_cast hq0.ne'`.

Conclude with `pow_ne_zero _ this`. Establish `hnq : ‖((q : ℂ) ^ a)‖ = (q : ℝ) ^ a` using `by simp`. Establish `: (∑ u ∈ univ.filter (fun u => Q u = 0), f u) - (∑ u, f u) / ((q : ℂ) ^ a) = ((∑ u ∈ univ.filter (fun u => Q u = 0), f u) * ((q : ℂ) ^ a) - ∑ u, f u) / ((q : ℂ) ^ a)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this, norm_div, hnq, ← mul_div_assoc]`.

Use `gcongr`.
-/
lemma gauss_core {U T : Type} [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (f : U → ℂ) (cond : AddChar T ℂ → ℕ) (q a ρ : ℕ)
    (hq : 2 ≤ q) (hρ : 4 ≤ ρ) (hT : Fintype.card T = q ^ a)
    (hc0 : ∀ ψ, cond ψ = 0 ↔ ψ = 0)
    (hcnt : ∀ i, 1 ≤ i → ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) ≤ (q : ℝ) ^ i)
    (hS : ∀ ψ : AddChar T ℂ, ψ ≠ 0 →
      ‖∑ u, ψ (Q u) * f u‖ ≤ ((q : ℝ) ^ (cond ψ * ρ))⁻¹ * (Fintype.card U : ℝ)) :
    ‖(∑ u ∈ univ.filter (fun u => Q u = 0), f u) - (∑ u, f u) / ((q : ℂ) ^ a)‖
      ≤ 2 * (q : ℝ) ^ (1 - (ρ : ℤ)) * ((Fintype.card U : ℝ) / (q : ℝ) ^ a) := by
  obtain ⟨hy, hy0, hy8⟩ := y_facts q ρ hq hρ
  set y : ℝ := (q : ℝ) ^ (1 - (ρ : ℤ))
  have hq0 : (0 : ℝ) < q := by positivity
  set g : ℕ → ℝ := fun i => if i = 0 then 0 else ((q : ℝ) ^ (i * ρ))⁻¹ with hg
  set B : ℕ → ℝ := fun i => if i = 0 then 0 else y ^ i with hB
  have hgB : ∀ i, ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) * g i ≤ B i := by
    intro i
    by_cases hi : i = 0
    · simp [hg, hB, hi]
    · simp only [hg, hB, if_neg hi]
      have : y ^ i = (q : ℝ) ^ i * ((q : ℝ) ^ (i * ρ))⁻¹ := by
        rw [hy, mul_pow, inv_pow, ← pow_mul, mul_comm ρ i]
      rw [this]
      gcongr
      exact hcnt i (Nat.one_le_iff_ne_zero.2 hi)
  obtain ⟨N, hN⟩ := sum_cond_le cond g B hgB
  have hsumB : ∑ i ∈ range (N + 1), B i ≤ 2 * y := by
    rw [Finset.sum_range_succ']
    simp only [hB, if_true, add_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
    have := geo_half y hy0 (by linarith) N
    have h2 : ∑ k ∈ range N, y ^ (k + 1) = y * ∑ k ∈ range N, y ^ k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [h2]
    have h3 : 0 ≤ y ^ N := pow_nonneg hy0 _
    nlinarith
  have hmain : ‖(∑ u ∈ univ.filter (fun u => Q u = 0), f u) * ((q : ℂ) ^ a) - ∑ u, f u‖
      ≤ 2 * y * (Fintype.card U : ℝ) := by
    have h0 := orth_sum Q f
    rw [hT, ← Finset.add_sum_erase univ _ (Finset.mem_univ (0 : AddChar T ℂ))] at h0
    simp only [AddChar.zero_apply, one_mul] at h0
    push_cast at h0
    rw [h0, add_sub_cancel_left]
    calc _ ≤ ∑ ψ ∈ univ.erase (0 : AddChar T ℂ), ‖∑ u, ψ (Q u) * f u‖ := norm_sum_le _ _
      _ ≤ ∑ ψ ∈ univ.erase (0 : AddChar T ℂ), g (cond ψ) * (Fintype.card U : ℝ) := by
          refine Finset.sum_le_sum fun ψ hψ => ?_
          have hψ0 : ψ ≠ 0 := (Finset.mem_erase.1 hψ).1
          have : cond ψ ≠ 0 := fun h => hψ0 ((hc0 ψ).1 h)
          simp only [hg, if_neg this]
          exact hS ψ hψ0
      _ ≤ ∑ ψ, g (cond ψ) * (Fintype.card U : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun ψ _ _ => ?_
          simp only [hg]; split_ifs <;> positivity
      _ = (∑ ψ, g (cond ψ)) * (Fintype.card U : ℝ) := by rw [Finset.sum_mul]
      _ ≤ _ := by
          gcongr
          exact (hN (N + 1) (by omega)).trans hsumB
  have hqa : ((q : ℂ) ^ a) ≠ 0 := by
    have : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
    exact pow_ne_zero _ this
  have hnq : ‖((q : ℂ) ^ a)‖ = (q : ℝ) ^ a := by simp
  have : (∑ u ∈ univ.filter (fun u => Q u = 0), f u) - (∑ u, f u) / ((q : ℂ) ^ a)
      = ((∑ u ∈ univ.filter (fun u => Q u = 0), f u) * ((q : ℂ) ^ a) - ∑ u, f u) / ((q : ℂ) ^ a) := by
    field_simp
  rw [this, norm_div, hnq, ← mul_div_assoc]
  gcongr

/- English proof (translation)
Use `⟨3, ?_⟩` and prove the remaining obligations. Introduce `U T _ _ _ _ Q χ cond q a ρ hq hρ hT hc0 hcnt hχ hS1 hS2`. Take `⟨hy, hy0, hy8⟩` from `y_facts q ρ hq hρ`. Establish `c1` using `gauss_core Q (fun _ => 1) cond q a ρ hq hρ hT hc0 hcnt (by simpa using hS2)`. Establish `c2` using `gauss_core Q χ cond q a ρ hq hρ hT hc0 hcnt hS1`.

Use `set y : ℝ := (q : ℝ) ^ (1 - (ρ : ℤ))`. Use `set u0 : ℝ := (Fintype.card U : ℝ) / (q : ℝ) ^ a with hu0`. Establish `hu00 : 0 ≤ u0` using `by positivity`. Rewrite `c2` using `[hχ, zero_div, sub_zero]`. Establish `e1 : (∑ u ∈ univ.filter (fun u => Q u = 0), (1 : ℂ)) - (∑ u : U, (1 : ℂ)) / ((q : ℂ) ^ a) = ((((univ.filter fun u => Q u = 0).card : ℝ) - u0 : ℝ) : ℂ)`.

Simplify using `[hu0]`. Rewrite `c1` using `[e1, Complex.norm_real, Real.norm_eq_abs]`. Establish `hyu : 0 ≤ y * u0` using `mul_nonneg hy0 hu00`. Use `⟨c1.trans (by nlinarith), c2.trans ?_⟩` and prove the remaining obligations. Use `(abs_le.1 c1).1` as an intermediate fact.

Establish `h3 : y * u0 ≤ u0 / 8` using `by nlinarith`. Establish `h4 : (3 / 4) * u0 ≤ ((univ.filter fun u => Q u = 0).card : ℝ)` using `by nlinarith`. Establish `h5 : y * ((3 / 4) * u0) ≤ y * ((univ.filter fun u => Q u = 0).card : ℝ)` using `mul_le_mul_of_nonneg_left h4 hy0`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gauss_sum_share : GaussShare := by
  refine ⟨3, ?_⟩
  intro U T _ _ _ _ Q χ cond q a ρ hq hρ hT hc0 hcnt hχ hS1 hS2
  obtain ⟨hy, hy0, hy8⟩ := y_facts q ρ hq hρ
  have c1 := gauss_core Q (fun _ => 1) cond q a ρ hq hρ hT hc0 hcnt (by simpa using hS2)
  have c2 := gauss_core Q χ cond q a ρ hq hρ hT hc0 hcnt hS1
  set y : ℝ := (q : ℝ) ^ (1 - (ρ : ℤ))
  set u0 : ℝ := (Fintype.card U : ℝ) / (q : ℝ) ^ a with hu0
  have hu00 : 0 ≤ u0 := by positivity
  rw [hχ, zero_div, sub_zero] at c2
  have e1 : (∑ u ∈ univ.filter (fun u => Q u = 0), (1 : ℂ)) - (∑ u : U, (1 : ℂ)) / ((q : ℂ) ^ a)
      = ((((univ.filter fun u => Q u = 0).card : ℝ) - u0 : ℝ) : ℂ) := by
    simp [hu0]
  rw [e1, Complex.norm_real, Real.norm_eq_abs] at c1
  have hyu : 0 ≤ y * u0 := mul_nonneg hy0 hu00
  refine ⟨c1.trans (by nlinarith), c2.trans ?_⟩
  have := (abs_le.1 c1).1
  have h3 : y * u0 ≤ u0 / 8 := by nlinarith
  have h4 : (3 / 4) * u0 ≤ ((univ.filter fun u => Q u = 0).card : ℝ) := by nlinarith
  have h5 : y * ((3 / 4) * u0) ≤ y * ((univ.filter fun u => Q u = 0).card : ℝ) :=
    mul_le_mul_of_nonneg_left h4 hy0
  nlinarith

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Evaluate the numerical expressions. Consider the case `succ j ih`. Rewrite using `[Finset.sum_range_succ, pow_succ q j]`.

Establish `: 0 < q ^ j` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma geo_q (q : ℝ) (hq : 2 ≤ q) (j : ℕ) : ∑ i ∈ range (j + 1), q ^ i ≤ 2 * q ^ j - 1 := by
  induction j with
  | zero => simp; norm_num
  | succ j ih =>
    rw [Finset.sum_range_succ, pow_succ q j]
    have : 0 < q ^ j := by positivity
    nlinarith

/- English proof (translation)
Use `⟨3, ?_⟩` and prove the remaining obligations. Introduce `U T _ _ _ _ Q cond q a ρ j hq hρ hT hcnt hS`. Take `⟨hy, hy0, hy8⟩` from `y_facts q ρ hq hρ`. Use `set y : ℝ := (q : ℝ) ^ (1 - (ρ : ℤ))`. Establish `hq0 : (0 : ℝ) < q` using `by positivity`.

Establish `hq2 : (2 : ℝ) ≤ q` using `by exact_mod_cast hq`. Use `set g : ℕ → ℝ := fun i => ((q : ℝ) ^ ((i - j) * ρ))⁻¹ with hg`. Take `⟨N, hN⟩` from `sum_cond_le cond g (fun i => (q : ℝ) ^ i * g i) (fun i => by`. Establish `: 0 ≤ g i` using `by simp only [hg]; positivity`. Conclude with `mul_le_mul_of_nonneg_right (hcnt i) this)`.

Establish `hsumB : ∑ i ∈ range (j + 1 + N), (q : ℝ) ^ i * g i ≤ 3 * (q : ℝ) ^ j`. Rewrite using `[Finset.sum_range_add]`. Establish `h1 : ∑ i ∈ range (j + 1), (q : ℝ) ^ i * g i = ∑ i ∈ range (j + 1), (q : ℝ) ^ i`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `: i - j = 0` using `by have := Finset.mem_range.1 hi; omega`.

Simplify using `[hg, this]`. Establish `h2 : ∑ l ∈ range N, (q : ℝ) ^ (j + 1 + l) * g (j + 1 + l) = (q : ℝ) ^ j * (y * ∑ l ∈ range N, y ^ l)`. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `: j + 1 + l - j = l + 1` using `by omega`.

Simplify using `only [hg, this]`. Rewrite using `[hy, ← pow_succ', mul_pow, inv_pow, ← pow_mul, mul_comm ρ (l + 1)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h2]`. Establish `h3` using `geo_q q hq2 j`.

Establish `h4` using `geo_half y hy0 (by linarith) N`. Establish `h5 : 0 ≤ y ^ N` using `pow_nonneg hy0 _`. Establish `h6 : y * ∑ l ∈ range N, y ^ l ≤ 1` using `by nlinarith`. Establish `h7 : 0 < (q : ℝ) ^ j` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h0` using `orth_sum Q (fun _ => (1 : ℂ))`. Simplify using `only [mul_one, Finset.sum_const, nsmul_eq_mul] at h0`. Establish `h1 : ((univ.filter fun u => Q u = 0).card : ℝ) * (q : ℝ) ^ a ≤ 3 * (q : ℝ) ^ j * (Fintype.card U : ℝ)`. Establish `: ((univ.filter fun u => Q u = 0).card : ℝ) * (q : ℝ) ^ a = ‖((univ.filter fun u => Q u = 0).card : ℂ) * (Fintype.card T : ℂ)‖`. Rewrite using `[hT]`.

Simplify using the standard rewrite rules. Rewrite using `[this, h0]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(hN (j + 1 + N) (by omega)).trans hsumB`. Rewrite using `[← mul_div_assoc, le_div_iff₀ (by positivity)]`.

Conclude with `h1`.
-/
theorem leakage_share_bound_alt : LeakShare := by
  refine ⟨3, ?_⟩
  intro U T _ _ _ _ Q cond q a ρ j hq hρ hT hcnt hS
  obtain ⟨hy, hy0, hy8⟩ := y_facts q ρ hq hρ
  set y : ℝ := (q : ℝ) ^ (1 - (ρ : ℤ))
  have hq0 : (0 : ℝ) < q := by positivity
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  set g : ℕ → ℝ := fun i => ((q : ℝ) ^ ((i - j) * ρ))⁻¹ with hg
  obtain ⟨N, hN⟩ := sum_cond_le cond g (fun i => (q : ℝ) ^ i * g i) (fun i => by
    have : 0 ≤ g i := by simp only [hg]; positivity
    exact mul_le_mul_of_nonneg_right (hcnt i) this)
  have hsumB : ∑ i ∈ range (j + 1 + N), (q : ℝ) ^ i * g i ≤ 3 * (q : ℝ) ^ j := by
    rw [Finset.sum_range_add]
    have h1 : ∑ i ∈ range (j + 1), (q : ℝ) ^ i * g i = ∑ i ∈ range (j + 1), (q : ℝ) ^ i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have : i - j = 0 := by have := Finset.mem_range.1 hi; omega
      simp [hg, this]
    have h2 : ∑ l ∈ range N, (q : ℝ) ^ (j + 1 + l) * g (j + 1 + l) = (q : ℝ) ^ j * (y * ∑ l ∈ range N, y ^ l) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have : j + 1 + l - j = l + 1 := by omega
      simp only [hg, this]
      rw [hy, ← pow_succ', mul_pow, inv_pow, ← pow_mul, mul_comm ρ (l + 1)]
      ring
    rw [h1, h2]
    have h3 := geo_q q hq2 j
    have h4 := geo_half y hy0 (by linarith) N
    have h5 : 0 ≤ y ^ N := pow_nonneg hy0 _
    have h6 : y * ∑ l ∈ range N, y ^ l ≤ 1 := by nlinarith
    have h7 : 0 < (q : ℝ) ^ j := by positivity
    nlinarith
  have h0 := orth_sum Q (fun _ => (1 : ℂ))
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h0
  have h1 : ((univ.filter fun u => Q u = 0).card : ℝ) * (q : ℝ) ^ a ≤ 3 * (q : ℝ) ^ j * (Fintype.card U : ℝ) := by
    have : ((univ.filter fun u => Q u = 0).card : ℝ) * (q : ℝ) ^ a
        = ‖((univ.filter fun u => Q u = 0).card : ℂ) * (Fintype.card T : ℂ)‖ := by
      rw [hT]; simp
    rw [this, h0]
    calc _ ≤ ∑ ψ : AddChar T ℂ, ‖∑ u, ψ (Q u)‖ := norm_sum_le _ _
      _ ≤ ∑ ψ : AddChar T ℂ, g (cond ψ) * (Fintype.card U : ℝ) := Finset.sum_le_sum fun ψ _ => hS ψ
      _ = (∑ ψ : AddChar T ℂ, g (cond ψ)) * (Fintype.card U : ℝ) := by rw [Finset.sum_mul]
      _ ≤ _ := by
          gcongr
          exact (hN (j + 1 + N) (by omega)).trans hsumB
  rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
  exact h1

/- English proof (translation)
Establish `key` using `(Fintype.linearIndependent_iffₛ.mp hli) (Sum.elim p q) (Sum.elim p' q') (by simpa [Fintype.sum_sum_type, Finset.sum_add_distrib] using h)`. Conclude with `fun i => ⟨key (Sum.inl i), key (Sum.inr i)⟩`.
-/
private lemma rep_eq {K V : Type} [CommRing K] [AddCommGroup V] [Module K V] (n : ℕ)
    (f f' : Fin n → V) (hli : LinearIndependent K (Sum.elim f f')) (p q p' q' : Fin n → K)
    (h : ∑ i, (p i • f i + q i • f' i) = ∑ i, (p' i • f i + q' i • f' i)) :
    ∀ i, p i = p' i ∧ q i = q' i := by
  have key := (Fintype.linearIndependent_iffₛ.mp hli) (Sum.elim p q) (Sum.elim p' q')
    (by simpa [Fintype.sum_sum_type, Finset.sum_add_distrib] using h)
  exact fun i => ⟨key (Sum.inl i), key (Sum.inr i)⟩

/- English proof (translation)
Introduce `K V _ _ _ O θ hθ n f f' hli α α'`. Use `set ti : K := ((θ⁻¹ : Kˣ) : K) with hti`. Establish `hmi : (θ : K) * ti = 1` using `by simp [hti]`. Establish `hsmul : ∀ (o : O) (v : V), o • v = (o : K) • v` using `fun o v => rfl`. Establish `hL : ti • (∑ i, α i • f i + ∑ i, α' i • f' i) = ∑ i, ((ti * α i) • f i + (ti * α' i) • f' i)`.

Rewrite using `[smul_add, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]`. Simplify using `only [smul_smul]`. Establish `hM : ∀ b c : Fin n → K, ∑ i, b i • f i + ∑ i, c i • (ti • (f' i - f i)) = ∑ i, ((b i - ti * c i) • f i + (ti * c i) • f' i)`. Introduce `b c`. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `module`. Rewrite using `[← Set.Sum.elim_range, Submodule.mem_span_range_iff_exists_fun]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`.

Simplify using `only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hsmul] at hc`. Rewrite `hc` using `[hM, hL]`. Establish `hr` using `rep_eq n f f' hli _ _ _ _ hc`. Introduce `i`. Take `⟨h1, h2⟩` from `hr i`.

Establish `hc2 : α' i = (c (Sum.inr i) : K)`. Take the linear combination `(-(θ : K)) * h2 - (α' i - (c (Sum.inr i) : K)) * hmi`. Use `⟨hc2 ▸ (c (Sum.inr i)).2, (c (Sum.inl i) : K), (c (Sum.inl i)).2, ?_⟩` and prove the remaining obligations. Rewrite using `[hc2]`. Take the linear combination `(-(θ : K)) * h1 - (α i + (c (Sum.inr i) : K)) * hmi`.

Introduce `h choose h1 x hx hxe using h`. Use `⟨Sum.elim (fun i => ⟨x i, hx i⟩) (fun i => ⟨α' i, h1 i⟩), ?_⟩` and prove the remaining obligations. Simplify using `only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hsmul]`. Rewrite using `[hM, hL]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `congr 2`. Take the linear combination `(-ti) * hxe i - (x i) * hmi`.
-/
theorem span_character_ring : SpanCharRing := by
  intro K V _ _ _ O θ hθ n f f' hli α α'
  set ti : K := ((θ⁻¹ : Kˣ) : K) with hti
  have hmi : (θ : K) * ti = 1 := by simp [hti]
  have hsmul : ∀ (o : O) (v : V), o • v = (o : K) • v := fun o v => rfl
  have hL : ti • (∑ i, α i • f i + ∑ i, α' i • f' i) =
      ∑ i, ((ti * α i) • f i + (ti * α' i) • f' i) := by
    rw [smul_add, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    simp only [smul_smul]
  have hM : ∀ b c : Fin n → K, ∑ i, b i • f i + ∑ i, c i • (ti • (f' i - f i)) =
      ∑ i, ((b i - ti * c i) • f i + (ti * c i) • f' i) := by
    intro b c
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    module
  rw [← Set.Sum.elim_range, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hsmul] at hc
    rw [hM, hL] at hc
    have hr := rep_eq n f f' hli _ _ _ _ hc
    intro i
    obtain ⟨h1, h2⟩ := hr i
    have hc2 : α' i = (c (Sum.inr i) : K) := by
      linear_combination (-(θ : K)) * h2 - (α' i - (c (Sum.inr i) : K)) * hmi
    refine ⟨hc2 ▸ (c (Sum.inr i)).2, (c (Sum.inl i) : K), (c (Sum.inl i)).2, ?_⟩
    rw [hc2]
    linear_combination (-(θ : K)) * h1 - (α i + (c (Sum.inr i) : K)) * hmi
  · intro h
    choose h1 x hx hxe using h
    refine ⟨Sum.elim (fun i => ⟨x i, hx i⟩) (fun i => ⟨α' i, h1 i⟩), ?_⟩
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hsmul]
    rw [hM, hL]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    linear_combination (-ti) * hxe i - (x i) * hmi

/- English proof (translation)
Introduce `i j`. Set `M : Matrix (Fin m) (Fin m) O` to `Matrix.of fun a b => ⟨G a b, hG a b⟩`. Establish `: G = M.map O.subtype` using `by ext a b; rfl`. Rewrite using `[this, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]`. Conclude with `(M.adjugate i j).2`.
-/
lemma adj_mem {E : Type} [CommRing E] (O : Subring E) (m : ℕ) (G : Matrix (Fin m) (Fin m) E)
    (hG : ∀ i j, G i j ∈ O) : ∀ i j, G.adjugate i j ∈ O := by
  intro i j
  let M : Matrix (Fin m) (Fin m) O := Matrix.of fun a b => ⟨G a b, hG a b⟩
  have : G = M.map O.subtype := by ext a b; rfl
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
  exact (M.adjugate i j).2

/- English proof (translation)
Simplify using `[map_sum, LinearMap.sum_apply]`.
-/
lemma gram_pair {E : Type} [CommRing E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (m : ℕ) (f : Fin m → V) (c : Fin m → E) (j : Fin m) :
    h (∑ i, c i • f i) (f j) = ∑ i, c i * h (f i) (f j) := by
  simp [map_sum, LinearMap.sum_apply]

/- English proof (translation)
Introduce `E _ _ V _ _ h O m f c hG hp i`. Use `set G : Matrix (Fin m) (Fin m) E := Matrix.of fun a b => h (f a) (f b) with hGd`. Establish `hadj` using `adj_mem O m G hG`. Establish `h1 : Matrix.vecMul (Matrix.vecMul c G) G.adjugate = G.det • c`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]`.

Establish `h2` using `congrFun h1 i`. Rewrite `h2` using `[Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← h2]`. Simplify using `only [Matrix.vecMul, dotProduct]`. Use `O.sum_mem fun j _ => O.mul_mem ?_ (hadj j i)` and prove the remaining obligations.

Use `hp j` as an intermediate fact. Rewrite `this` using `[gram_pair]`. Conclude with `this`.
-/
theorem determinant_annihilates : DetKills := by
  intro E _ _ V _ _ h O m f c hG hp i
  set G : Matrix (Fin m) (Fin m) E := Matrix.of fun a b => h (f a) (f b) with hGd
  have hadj := adj_mem O m G hG
  have h1 : Matrix.vecMul (Matrix.vecMul c G) G.adjugate = G.det • c := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
  have h2 := congrFun h1 i
  rw [Pi.smul_apply, smul_eq_mul] at h2
  rw [← h2]
  simp only [Matrix.vecMul, dotProduct]
  refine O.sum_mem fun j _ => O.mul_mem ?_ (hadj j i)
  have := hp j
  rw [gram_pair] at this
  exact this

/- English proof (translation)
Introduce `E _ _ V _ _ h O m f hG ⟨d, hd, hdd⟩ v hp`. Use `set G : Matrix (Fin m) (Fin m) E := Matrix.of fun a b => h (f a) (f b) with hGd`. Establish `hadj` using `adj_mem O m G hG`. Use `set p : Fin m → E := fun j => h v (f j) with hpd`. Use `⟨fun i => d * Matrix.vecMul p G.adjugate i, fun i => ?_, fun j => ?_⟩` and prove the remaining obligations.

Use `O.mul_mem hd ?_` and prove the remaining obligations. Simplify using `only [Matrix.vecMul, dotProduct]`. Conclude with `O.sum_mem fun j _ => O.mul_mem (hp j) (hadj j i)`. Rewrite using `[map_sub, LinearMap.sub_apply, gram_pair]`. Establish `h1 : Matrix.vecMul (Matrix.vecMul p G.adjugate) G = G.det • p`.

Rewrite using `[Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul, Matrix.vecMul_one]`. Establish `h2` using `congrFun h1 j`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at h2`. Establish `h3 : ∑ i, d * Matrix.vecMul p G.adjugate i * h (f i) (f j) = d * Matrix.vecMul (Matrix.vecMul p G.adjugate) G j` using `by conv_rhs => rw [Matrix.vecMul, dotProduct, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [mul_assoc]; rfl`.

Rewrite using `[h3, h2, ← mul_assoc, hdd, one_mul, sub_self]`.
-/
theorem unimodular_split : UnimodSplit := by
  intro E _ _ V _ _ h O m f hG ⟨d, hd, hdd⟩ v hp
  set G : Matrix (Fin m) (Fin m) E := Matrix.of fun a b => h (f a) (f b) with hGd
  have hadj := adj_mem O m G hG
  set p : Fin m → E := fun j => h v (f j) with hpd
  refine ⟨fun i => d * Matrix.vecMul p G.adjugate i, fun i => ?_, fun j => ?_⟩
  · refine O.mul_mem hd ?_
    simp only [Matrix.vecMul, dotProduct]
    exact O.sum_mem fun j _ => O.mul_mem (hp j) (hadj j i)
  · rw [map_sub, LinearMap.sub_apply, gram_pair]
    have h1 : Matrix.vecMul (Matrix.vecMul p G.adjugate) G = G.det • p := by
      rw [Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul, Matrix.vecMul_one]
    have h2 := congrFun h1 j
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    have h3 : ∑ i, d * Matrix.vecMul p G.adjugate i * h (f i) (f j)
        = d * Matrix.vecMul (Matrix.vecMul p G.adjugate) G j := by
      conv_rhs => rw [Matrix.vecMul, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc]; rfl
    rw [h3, h2, ← mul_assoc, hdd, one_mul, sub_self]

/- English proof (translation)
Introduce `B _ s vh ve vt q A r hq hs hvh hve hvt hA1 hA2`. Establish `hq0 : 0 < q` using `by linarith`. Establish `hr : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← Real.rpow_mul hq0.le, ← Real.rpow_sum_of_pos hq0]`.

Apply `Real.rpow_le_rpow_of_exponent_le hq` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun b _ => ?_` and prove the remaining obligations. Establish `: (s b : ℝ) ≤ (r : ℝ) + 1` using `by exact_mod_cast (hs b).2`. Use `hvh b` as an intermediate fact.

Use `gcongr`. Use `_ = 2 * ((r : ℝ) + 1) * ∑ b, vh b := by rw [Finset.mul_sum]`. Use `_ ≤ 2 * ((r : ℝ) + 1) * A := by gcongr`. Use `_ = _ := by ring`. Rewrite using `[← Real.rpow_mul hq0.le, ← Real.rpow_sum_of_pos hq0]`.

Apply `Real.rpow_le_rpow_of_exponent_le hq` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun b _ => ?_` and prove the remaining obligations. Establish `h1 : (s b : ℝ) ≤ (r : ℝ) + 1` using `by exact_mod_cast (hs b).2`. Establish `h2 : (1 : ℝ) ≤ (s b : ℝ)` using `by exact_mod_cast (hs b).1`.

Establish `h3 : vt b * ((s b : ℝ) * ((s b : ℝ) - 1) / 2) = (ve b - vh b) * (((s b : ℝ) - 1) / 2)`. Rewrite using `[← hvt b]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3]`. Use `hvh b` as an intermediate fact.

Use `hve b` as an intermediate fact. Use polynomial arithmetic with `[mul_nonneg (hvh b) (sub_nonneg.2 h2), mul_nonneg (hve b) (sub_nonneg.2 h1)]`. Use `_ = ((r : ℝ) + 1) / 2 * ∑ b, ve b := by rw [Finset.mul_sum]`. Use `_ ≤ ((r : ℝ) + 1) / 2 * A := by gcongr`. Use `_ = _ := by ring`.
-/
theorem local_density_product : ValuationProductBound := by
  intro B _ s vh ve vt q A r hq hs hvh hve hvt hA1 hA2
  have hq0 : 0 < q := by linarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  constructor
  · rw [← Real.rpow_mul hq0.le, ← Real.rpow_sum_of_pos hq0]
    apply Real.rpow_le_rpow_of_exponent_le hq
    calc ∑ b, 2 * (s b : ℝ) * vh b ≤ ∑ b, 2 * ((r : ℝ) + 1) * vh b := by
          refine Finset.sum_le_sum fun b _ => ?_
          have : (s b : ℝ) ≤ (r : ℝ) + 1 := by exact_mod_cast (hs b).2
          have := hvh b
          gcongr
      _ = 2 * ((r : ℝ) + 1) * ∑ b, vh b := by rw [Finset.mul_sum]
      _ ≤ 2 * ((r : ℝ) + 1) * A := by gcongr
      _ = _ := by ring
  · rw [← Real.rpow_mul hq0.le, ← Real.rpow_sum_of_pos hq0]
    apply Real.rpow_le_rpow_of_exponent_le hq
    calc ∑ b, vt b * ((s b : ℝ) * ((s b : ℝ) - 1) / 2) ≤ ∑ b, ((r : ℝ) + 1) / 2 * ve b := by
          refine Finset.sum_le_sum fun b _ => ?_
          have h1 : (s b : ℝ) ≤ (r : ℝ) + 1 := by exact_mod_cast (hs b).2
          have h2 : (1 : ℝ) ≤ (s b : ℝ) := by exact_mod_cast (hs b).1
          have h3 : vt b * ((s b : ℝ) * ((s b : ℝ) - 1) / 2) = (ve b - vh b) * (((s b : ℝ) - 1) / 2) := by
            rw [← hvt b]; ring
          rw [h3]
          have := hvh b
          have := hve b
          nlinarith [mul_nonneg (hvh b) (sub_nonneg.2 h2), mul_nonneg (hve b) (sub_nonneg.2 h1)]
      _ = ((r : ℝ) + 1) / 2 * ∑ b, ve b := by rw [Finset.mul_sum]
      _ ≤ ((r : ℝ) + 1) / 2 * A := by gcongr
      _ = _ := by ring

/- English proof (translation)
Introduce `E _ _ V _ _ h O abelian₂ r e y hH htr hI he hy hd`. Establish `hg : ∀ j k, h (y j) (y k) ∈ O` using `fun j k => hI _ (hy j) _ (hy k)`. Establish `hdiag : ∀ j, ∃ s ∈ O, s + star s = h (y j) (y j)` using `fun j => htr _ (hg j j) (hH _ _).symm`. Use `choose s hs hss using hdiag`. Use `⟨fun j l => if j < l then h (y j) (y l) else if j = l then s j else 0, fun j l => ?_, fun j k => ?_⟩` and prove the remaining obligations.

Simplify using `only split_ifs`. Conclude with `hg j l`. Conclude with `hs j`. Conclude with `O.zero_mem`. Use `set c : Fin r → Fin r → E := fun j l => if j < l then h (y j) (y l) else if j = l then s j else 0 with hc`.

Establish `hd' : ∀ i j, h (e i) (y j) = if i = j then 1 else 0`. Apply the tactic sequence `intro i j; rw [hH (y j) (e i), hd]; split_ifs <;> simp`. Establish `expand : h (y j - ∑ l, c j l • e l) (y k - ∑ l, c k l • e l) = h (y j) (y k) - star (c k j) - c j k`. Simplify using `only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, he, hd, hd', smul_eq_mul, starRingEnd_apply]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[expand]`. Break down `lt_trichotomy j k with hjk | hjk | hjk` into its components or cases. Establish `h1 : c j k = h (y j) (y k)` using `by simp [hc, hjk]`. Establish `h2 : c k j = 0` using `by simp [hc, hjk.not_gt, hjk.ne']`.

Rewrite using `[h1, h2]`. Simplify using the standard rewrite rules. Substitute `hjk` using the available equality. Establish `h1 : c j j = s j` using `by simp [hc]`. Rewrite using `[h1, ← hss j]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h1 : c j k = 0` using `by simp [hc, hjk.not_gt, hjk.ne']`. Establish `h2 : c k j = h (y k) (y j)` using `by simp [hc, hjk]`. Rewrite using `[h1, h2, ← hH]`. Simplify using the standard rewrite rules.
-/
theorem isotropic_complement : IsoComplement := by
  intro E _ _ V _ _ h O abelian₂ r e y hH htr hI he hy hd
  have hg : ∀ j k, h (y j) (y k) ∈ O := fun j k => hI _ (hy j) _ (hy k)
  have hdiag : ∀ j, ∃ s ∈ O, s + star s = h (y j) (y j) := fun j => htr _ (hg j j) (hH _ _).symm
  choose s hs hss using hdiag
  refine ⟨fun j l => if j < l then h (y j) (y l) else if j = l then s j else 0, fun j l => ?_, fun j k => ?_⟩
  · dsimp only
    split_ifs
    · exact hg j l
    · exact hs j
    · exact O.zero_mem
  · set c : Fin r → Fin r → E := fun j l => if j < l then h (y j) (y l) else if j = l then s j else 0 with hc
    have hd' : ∀ i j, h (e i) (y j) = if i = j then 1 else 0 := by
      intro i j; rw [hH (y j) (e i), hd]; split_ifs <;> simp
    have expand : h (y j - ∑ l, c j l • e l) (y k - ∑ l, c k l • e l)
        = h (y j) (y k) - star (c k j) - c j k := by
      simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, map_smul,
        LinearMap.smul_apply, LinearMap.map_smulₛₗ, he, hd, hd', smul_eq_mul, starRingEnd_apply]
      simp
      ring
    rw [expand]
    rcases lt_trichotomy j k with hjk | hjk | hjk
    · have h1 : c j k = h (y j) (y k) := by simp [hc, hjk]
      have h2 : c k j = 0 := by simp [hc, hjk.not_gt, hjk.ne']
      rw [h1, h2]; simp
    · subst hjk
      have h1 : c j j = s j := by simp [hc]
      rw [h1, ← hss j]; ring
    · have h1 : c j k = 0 := by simp [hc, hjk.not_gt, hjk.ne']
      have h2 : c k j = h (y k) (y j) := by simp [hc, hjk]
      rw [h1, h2, ← hH]; simp

/- English proof (translation)
Introduce `E _ n m A`. Use `LinearMap.det_pi (R := E) (ι := Fin n) (M := Fin m → E) (fun _ => Matrix.vecMulLinear A)` as an intermediate fact. Rewrite `this` using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Establish `hA : LinearMap.det (Matrix.vecMulLinear A) = A.det`. Rewrite using `[← Matrix.det_transpose A, ← LinearMap.det_toLin' A.transpose]`.

Use `congr 1`. Use extensionality with `v i`. Simplify using `[Matrix.vecMulLinear, Matrix.toLin'_apply]`. Rewrite `this` using `[hA]`. Rewrite using `[← this]`.

Both sides reduce to the same expression.
-/
theorem tuple_jacobian_alt : TupleJac := by
  intro E _ n m A
  have := LinearMap.det_pi (R := E) (ι := Fin n) (M := Fin m → E) (fun _ => Matrix.vecMulLinear A)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  have hA : LinearMap.det (Matrix.vecMulLinear A) = A.det := by
    rw [← Matrix.det_transpose A, ← LinearMap.det_toLin' A.transpose]
    congr 1
    ext v i
    simp [Matrix.vecMulLinear, Matrix.toLin'_apply]
  rw [hA] at this
  rw [← this]
  rfl

/- English proof (translation)
Rewrite using `[inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x]`. Both sides reduce to the same expression.
-/
lemma norm_sq_c {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : V) :
    ((‖x‖ : ℝ) : ℂ) ^ 2 = inner ℂ x x := by
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x]; rfl

/- English proof (translation)
Introduce `ι _ s _ _ _ V _ _ v`. Use `push_cast`. Establish `h1 : ∀ c : Quotient s, ((‖∑ i ∈ univ.filter (fun i => Quotient.mk s i = c), v i‖ : ℂ)) ^ 2 = ∑ i ∈ univ.filter (fun i => Quotient.mk s i = c), ∑ j, if s.r i j then inner ℂ (v i) (v j) else 0`. Introduce `c`. Rewrite using `[norm_sq_c, sum_inner]`.

Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[inner_sum, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hi'` using `(Finset.mem_filter.1 hi).2`. Establish `: (Quotient.mk s j = c) ↔ s.r i j`.

Rewrite using `[← hi', Quotient.eq]`. Conclude with `⟨fun h => s.symm h, fun h => s.symm h⟩`. Simplify using `only [this]`. Repeatedly rewrite using `[h1]`. Rewrite using `[Finset.sum_fiberwise]`.
-/
theorem class_number_squares : ClassSquares := by
  intro ι _ s _ _ _ V _ _ v
  push_cast
  have h1 : ∀ c : Quotient s, ((‖∑ i ∈ univ.filter (fun i => Quotient.mk s i = c), v i‖ : ℂ)) ^ 2
      = ∑ i ∈ univ.filter (fun i => Quotient.mk s i = c),
          ∑ j, if s.r i j then inner ℂ (v i) (v j) else 0 := by
    intro c
    rw [norm_sq_c, sum_inner]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [inner_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hi' := (Finset.mem_filter.1 hi).2
    have : (Quotient.mk s j = c) ↔ s.r i j := by
      rw [← hi', Quotient.eq]; exact ⟨fun h => s.symm h, fun h => s.symm h⟩
    simp only [this]
  simp_rw [h1]
  rw [Finset.sum_fiberwise]

/- English proof (translation)
Introduce `S _ _ _ n Gm ψ φ hdet hφ hadd`. Use `set yv : (Fin n → S) → Fin n → S := fun d => Gm.mulVec (fun j => star (d j)) with hyv`. Establish `hB : ∀ u d : Fin n → S, ∑ i, ∑ j, u i * Gm i j * star (d j) = ∑ i, u i * yv d i`. Introduce `u d`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [hyv, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Simplify using `only [hB] at hadd`. Use `set T : (Fin n → S) → ℂ := fun d => ∑ v : Fin n → S, ψ (∑ i, v i * yv d i) with hT`. Establish `h1 : ((‖∑ u, φ u‖ ^ 2 : ℝ) : ℂ) = ∑ d, φ d * T d`. Use `push_cast`.

Rewrite using `[← Complex.mul_conj', map_sum, Finset.sum_mul_sum, Finset.sum_comm]`. Establish `: ∀ v : Fin n → S, ∑ u, φ u * (starRingEnd ℂ) (φ v) = ∑ d, φ d * ψ (∑ i, v i * yv d i)`. Introduce `v`. Rewrite using `[← Fintype.sum_equiv (Equiv.addLeft v) (fun d => φ (v + d) * (starRingEnd ℂ) (φ v)) _ (fun d => rfl)]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations.

Rewrite using `[hadd]`. Establish `: φ v * (starRingEnd ℂ) (φ v) = 1` using `by rw [Complex.mul_conj', hφ]; simp`. Take the linear combination `(φ d * ψ (∑ i, v i * yv d i)) * this`. Repeatedly rewrite using `[this, hT, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Establish `hTle : ∀ d, ‖T d‖ ≤ (Fintype.card S : ℝ) ^ n`. Introduce `d`. Combine the equalities or inequalities in the displayed calculation. Establish `hT0 : ∀ d, (¬ ∀ i c, ψ (c * yv d i) = 1) → T d = 0`. Introduce `d hd`.

Use `push Not at hd`. Take `⟨i, c, hc⟩` from `hd`. Establish `: T d = ψ (c * yv d i) * T d` using `by conv_lhs => rw [hT]`. Simplify using `only`. Rewrite using `[← Fintype.sum_equiv (Equiv.addRight (Pi.single i c : Fin n → S)) (fun v : Fin n → S => ψ (∑ k, (v + (Pi.single i c : Fin n → S)) k * yv d k)) _ (fun v => rfl), hT, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← AddChar.map_add_eq_mul]`. Use `congr 1`. Simplify using `only [Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Rewrite using `[add_comm]`.

Use `congr 1`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Simplify using `[Pi.single_eq_of_ne hk]`.

Simplify using the standard rewrite rules. Establish `h2 : (1 - ψ (c * yv d i)) * T d = 0` using `by linear_combination this`. Break down `mul_eq_zero.1 h2 with h3 | h3` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h3).symm hc`. Conclude with `h3`.

Establish `hinj : Function.Injective yv`. Introduce `d d' hdd`. Establish `h3 : ∀ x : Fin n → S, Gm⁻¹.mulVec (Gm.mulVec x) = x` using `fun x => by`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Gm hdet, Matrix.one_mulVec]`. Establish `h4 : (fun j => star (d j)) = fun j => star (d' j)`.

Rewrite using `[← h3 (fun j => star (d j)), ← h3 (fun j => star (d' j))]`. Conclude with `congrArg _ hdd`. Use extensionality with `j`. Conclude with `star_injective (congrFun h4 j)`. Establish `hcount : ((univ.filter fun d => ∀ i c, ψ (c * yv d i) = 1).card : ℝ) ≤ (Nat.card {y : S // ∀ c, ψ (c * y) = 1} : ℝ) ^ n`.

Establish `: (univ.filter fun d => ∀ i c, ψ (c * yv d i) = 1).card ≤ Nat.card (Fin n → {y : S // ∀ c, ψ (c * y) = 1})`. Rewrite using `[← Fintype.card_subtype, ← Nat.card_eq_fintype_card]`. Use `Nat.card_le_card_of_injective (fun d : {d // ∀ i c, ψ (c * yv d i) = 1} => fun i => (⟨yv d.1 i, d.2 i⟩ : {y : S // ∀ c, ψ (c * y) = 1})) ?_` and prove the remaining obligations. Introduce `d d' hdd`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `hinj` to reduce the goal to its premises. Use extensionality with `i`. Conclude with `congrArg Subtype.val (congrFun hdd i)`. Rewrite `this` using `[Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]`. Conclude with `this` after adjusting the coercions.

Establish `h2 : ‖∑ u, φ u‖ ^ 2 = ‖∑ d, φ d * T d‖`. Rewrite using `[← h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]`. Rewrite using `[h2]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun d _ => ?_` and prove the remaining obligations.

Use `split_ifs with hd`. Conclude with `hTle d`. Rewrite using `[hT0 d hd, norm_zero]`. Use `_ = ((univ.filter fun d => ∀ i c, ψ (c * yv d i) = 1).card : ℝ) * (Fintype.card S : ℝ) ^ n := by`. Rewrite using `[← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]`.

Use `_ ≤ _ := by`. Rewrite using `[mul_comm]`. Use `gcongr`.
-/
theorem hermitian_gauss_sum_ring : HermGaussRing := by
  intro S _ _ _ n Gm ψ φ hdet hφ hadd
  classical
  set yv : (Fin n → S) → Fin n → S := fun d => Gm.mulVec (fun j => star (d j)) with hyv
  have hB : ∀ u d : Fin n → S, ∑ i, ∑ j, u i * Gm i j * star (d j) = ∑ i, u i * yv d i := by
    intro u d
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hyv, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  simp only [hB] at hadd
  set T : (Fin n → S) → ℂ := fun d => ∑ v : Fin n → S, ψ (∑ i, v i * yv d i) with hT
  have h1 : ((‖∑ u, φ u‖ ^ 2 : ℝ) : ℂ) = ∑ d, φ d * T d := by
    push_cast
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, Finset.sum_comm]
    have : ∀ v : Fin n → S, ∑ u, φ u * (starRingEnd ℂ) (φ v) = ∑ d, φ d * ψ (∑ i, v i * yv d i) := by
      intro v
      rw [← Fintype.sum_equiv (Equiv.addLeft v) (fun d => φ (v + d) * (starRingEnd ℂ) (φ v)) _ (fun d => rfl)]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [hadd]
      have : φ v * (starRingEnd ℂ) (φ v) = 1 := by rw [Complex.mul_conj', hφ]; simp
      linear_combination (φ d * ψ (∑ i, v i * yv d i)) * this
    simp_rw [this, hT, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hTle : ∀ d, ‖T d‖ ≤ (Fintype.card S : ℝ) ^ n := by
    intro d
    calc ‖T d‖ ≤ ∑ v : Fin n → S, ‖ψ (∑ i, v i * yv d i)‖ := norm_sum_le _ _
      _ = _ := by simp [AddChar.norm_apply]
  have hT0 : ∀ d, (¬ ∀ i c, ψ (c * yv d i) = 1) → T d = 0 := by
    intro d hd
    push Not at hd
    obtain ⟨i, c, hc⟩ := hd
    have : T d = ψ (c * yv d i) * T d := by
      conv_lhs => rw [hT]
      simp only
      rw [← Fintype.sum_equiv (Equiv.addRight (Pi.single i c : Fin n → S))
        (fun v : Fin n → S => ψ (∑ k, (v + (Pi.single i c : Fin n → S)) k * yv d k)) _ (fun v => rfl), hT, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      rw [add_comm]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk; simp [Pi.single_eq_of_ne hk]
      · simp
    have h2 : (1 - ψ (c * yv d i)) * T d = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (sub_eq_zero.1 h3).symm hc
    · exact h3
  have hinj : Function.Injective yv := by
    intro d d' hdd
    have h3 : ∀ x : Fin n → S, Gm⁻¹.mulVec (Gm.mulVec x) = x := fun x => by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Gm hdet, Matrix.one_mulVec]
    have h4 : (fun j => star (d j)) = fun j => star (d' j) := by
      rw [← h3 (fun j => star (d j)), ← h3 (fun j => star (d' j))]
      exact congrArg _ hdd
    ext j
    exact star_injective (congrFun h4 j)
  have hcount : ((univ.filter fun d => ∀ i c, ψ (c * yv d i) = 1).card : ℝ)
      ≤ (Nat.card {y : S // ∀ c, ψ (c * y) = 1} : ℝ) ^ n := by
    have : (univ.filter fun d => ∀ i c, ψ (c * yv d i) = 1).card
        ≤ Nat.card (Fin n → {y : S // ∀ c, ψ (c * y) = 1}) := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      refine Nat.card_le_card_of_injective
        (fun d : {d // ∀ i c, ψ (c * yv d i) = 1} => fun i => (⟨yv d.1 i, d.2 i⟩ : {y : S // ∀ c, ψ (c * y) = 1})) ?_
      intro d d' hdd
      apply Subtype.ext
      apply hinj
      ext i
      exact congrArg Subtype.val (congrFun hdd i)
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this
    exact_mod_cast this
  have h2 : ‖∑ u, φ u‖ ^ 2 = ‖∑ d, φ d * T d‖ := by
    rw [← h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [h2]
  calc ‖∑ d, φ d * T d‖ ≤ ∑ d, ‖φ d * T d‖ := norm_sum_le _ _
    _ = ∑ d, ‖T d‖ := by simp [hφ]
    _ ≤ ∑ d, if (∀ i c, ψ (c * yv d i) = 1) then (Fintype.card S : ℝ) ^ n else 0 := by
        refine Finset.sum_le_sum fun d _ => ?_
        split_ifs with hd
        · exact hTle d
        · rw [hT0 d hd, norm_zero]
    _ = ((univ.filter fun d => ∀ i c, ψ (c * yv d i) = 1).card : ℝ) * (Fintype.card S : ℝ) ^ n := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        rw [mul_comm]
        gcongr

/- English proof (translation)
Introduce `O B _ _ _ _ q hq I hI`. Establish `hcard : Nat.card B = Nat.card (B ⧸ I) * Nat.card I`. Use `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup I.toAddSubgroup` as an intermediate fact. Conclude with `this`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, b ∉ I := by`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hI (eq_top_iff.2 fun x _ => hcon x)`. Use `set x : B ⧸ I := I.mkQ b with hx`. Establish `hx0 : x ≠ 0`.

Rewrite using `[hx, Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]`. Conclude with `hb`. Use `set f : O →ₗ[O] (B ⧸ I) := LinearMap.toSpanSingleton O (B ⧸ I) x with hf`. Use `set J : Ideal O := LinearMap.ker f with hJ`. Establish `hJtop : J ≠ ⊤`.

Introduce `h`. Establish `: (1 : O) ∈ J` using `by rw [h]; trivial`. Rewrite `this` using `[hJ, LinearMap.mem_ker, hf, LinearMap.toSpanSingleton_apply, one_smul]`. Conclude with `hx0 this`. Take `⟨P, hP, hJP⟩` from `Ideal.exists_le_maximal J hJtop`.

Establish `hinj : Function.Injective (J.liftQ f le_rfl)`. Rewrite using `[← LinearMap.ker_eq_bot]`. Conclude with `Submodule.ker_liftQ_eq_bot _ _ _ le_rfl`. Establish `: Finite (B ⧸ I)` using `Finite.of_surjective _ I.mkQ_surjective`. Establish `: Finite (O ⧸ J)` using `Finite.of_injective _ hinj`.

Establish `h1 : Nat.card (O ⧸ J) ≤ Nat.card (B ⧸ I)` using `Nat.card_le_card_of_injective _ hinj`. Establish `h2 : Nat.card (O ⧸ P) ≤ Nat.card (O ⧸ J)` using `Nat.card_le_card_of_surjective (Ideal.Quotient.factor hJP) (Ideal.Quotient.factor_surjective hJP)`. Rewrite using `[hcard]`. Conclude with `Nat.mul_le_mul_right _ ((hq P hP).trans (h2.trans h1))`.
-/
theorem proper_index_formula : ProperIndex := by
  intro O B _ _ _ _ q hq I hI
  have hcard : Nat.card B = Nat.card (B ⧸ I) * Nat.card I := by
    have := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup I.toAddSubgroup
    exact this
  obtain ⟨b, hb⟩ : ∃ b, b ∉ I := by
    by_contra hcon
    push Not at hcon
    exact hI (eq_top_iff.2 fun x _ => hcon x)
  set x : B ⧸ I := I.mkQ b with hx
  have hx0 : x ≠ 0 := by
    rw [hx, Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]; exact hb
  set f : O →ₗ[O] (B ⧸ I) := LinearMap.toSpanSingleton O (B ⧸ I) x with hf
  set J : Ideal O := LinearMap.ker f with hJ
  have hJtop : J ≠ ⊤ := by
    intro h
    have : (1 : O) ∈ J := by rw [h]; trivial
    rw [hJ, LinearMap.mem_ker, hf, LinearMap.toSpanSingleton_apply, one_smul] at this
    exact hx0 this
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJtop
  have hinj : Function.Injective (J.liftQ f le_rfl) := by
    rw [← LinearMap.ker_eq_bot]; exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have : Finite (B ⧸ I) := Finite.of_surjective _ I.mkQ_surjective
  have : Finite (O ⧸ J) := Finite.of_injective _ hinj
  have h1 : Nat.card (O ⧸ J) ≤ Nat.card (B ⧸ I) := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (O ⧸ P) ≤ Nat.card (O ⧸ J) :=
    Nat.card_le_card_of_surjective (Ideal.Quotient.factor hJP) (Ideal.Quotient.factor_surjective hJP)
  rw [hcard]
  exact Nat.mul_le_mul_right _ ((hq P hP).trans (h2.trans h1))

/- English proof (translation)
Introduce `K _ _ I`. Use `UniqueFactorizationMonoid.induction_on_prime (P := fun I : Ideal (NumberField.RingOfIntegers K) => I ≠ ⊥ → {J : Ideal (NumberField.RingOfIntegers K) | J ∣ I}.Finite ∧ {J : Ideal (NumberField.RingOfIntegers K) | J ∣ I}.ncard ≤ Ideal.absNorm I) I ?_ ?_ ?_` and prove the remaining obligations. Introduce `h`. Conclude with `absurd Ideal.zero_eq_bot h`. Introduce `x hx _`.

Establish `hx' : x = ⊤` using `Ideal.isUnit_iff.1 hx`. Establish `: {J : Ideal (NumberField.RingOfIntegers K) | J ∣ x} = {⊤}`. Use extensionality with `J`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `Ideal.isUnit_iff.1 (isUnit_of_dvd_unit h hx)`. Introduce and unpack `rfl`. Rewrite using `[hx']`. Rewrite using `[this, hx']`.

Simplify using the standard rewrite rules. Introduce `a p ha hp ih _`. Take `⟨hfin, hle⟩` from `ih (by rwa [← Ideal.zero_eq_bot])`. Establish `hsub : {J : Ideal (NumberField.RingOfIntegers K) | J ∣ p * a} ⊆ {J | J ∣ a} ∪ (fun J => p * J) '' {J | J ∣ a}`. Introduce `J hJ`.

Distinguish the cases in `hpJ : p ∣ J`. Take `⟨J', rfl⟩` from `hpJ`. Conclude with `Or.inr ⟨J', (mul_dvd_mul_iff_left hp.ne_zero).1 hJ, rfl⟩`. Use `left`. Take `⟨c, hc⟩` from `hJ`.

Establish `: p ∣ J * c` using `⟨a, hc.symm⟩`. Break down `hp.dvd_or_dvd this with h | ⟨c', rfl⟩` into its components or cases. Conclude with `absurd h hpJ`. Use `⟨c', ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hp.ne_zero` to reduce the goal to its premises.

Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfin2 : ({J | J ∣ a} ∪ (fun J => p * J) '' {J | J ∣ a}).Finite` using `hfin.union (hfin.image _)`. Use `⟨hfin2.subset hsub, ?_⟩` and prove the remaining obligations. Establish `hp2 : 2 ≤ Ideal.absNorm p`.

Establish `h0 : Ideal.absNorm p ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]`. Conclude with `hp.ne_zero`. Establish `h1 : Ideal.absNorm p ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff, ← Ideal.isUnit_iff]`.

Conclude with `hp.not_isUnit`. Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation. Conclude with `Nat.add_le_add_left (Set.ncard_image_le hfin) _`. Use `_ = 2 * {J | J ∣ a}.ncard := by ring`.

Use `_ ≤ Ideal.absNorm p * Ideal.absNorm a := Nat.mul_le_mul hp2 hle`. Use `_ = _ := (map_mul _ _ _).symm`.
-/
theorem divisor_count_bound : DivisorCount := by
  intro K _ _ I
  refine UniqueFactorizationMonoid.induction_on_prime (P := fun I : Ideal (NumberField.RingOfIntegers K) =>
    I ≠ ⊥ → {J : Ideal (NumberField.RingOfIntegers K) | J ∣ I}.Finite ∧
    {J : Ideal (NumberField.RingOfIntegers K) | J ∣ I}.ncard ≤ Ideal.absNorm I) I ?_ ?_ ?_
  · intro h; exact absurd Ideal.zero_eq_bot h
  · intro x hx _
    have hx' : x = ⊤ := Ideal.isUnit_iff.1 hx
    have : {J : Ideal (NumberField.RingOfIntegers K) | J ∣ x} = {⊤} := by
      ext J
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro h; exact Ideal.isUnit_iff.1 (isUnit_of_dvd_unit h hx)
      · rintro rfl; rw [hx']
    rw [this, hx']
    simp
  · intro a p ha hp ih _
    obtain ⟨hfin, hle⟩ := ih (by rwa [← Ideal.zero_eq_bot])
    have hsub : {J : Ideal (NumberField.RingOfIntegers K) | J ∣ p * a}
        ⊆ {J | J ∣ a} ∪ (fun J => p * J) '' {J | J ∣ a} := by
      intro J hJ
      by_cases hpJ : p ∣ J
      · obtain ⟨J', rfl⟩ := hpJ
        exact Or.inr ⟨J', (mul_dvd_mul_iff_left hp.ne_zero).1 hJ, rfl⟩
      · left
        obtain ⟨c, hc⟩ := hJ
        have : p ∣ J * c := ⟨a, hc.symm⟩
        rcases hp.dvd_or_dvd this with h | ⟨c', rfl⟩
        · exact absurd h hpJ
        · refine ⟨c', ?_⟩
          apply mul_left_cancel₀ hp.ne_zero
          rw [hc]; ring
    have hfin2 : ({J | J ∣ a} ∪ (fun J => p * J) '' {J | J ∣ a}).Finite := hfin.union (hfin.image _)
    refine ⟨hfin2.subset hsub, ?_⟩
    have hp2 : 2 ≤ Ideal.absNorm p := by
      have h0 : Ideal.absNorm p ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]; exact hp.ne_zero
      have h1 : Ideal.absNorm p ≠ 1 := by
        rw [Ne, Ideal.absNorm_eq_one_iff, ← Ideal.isUnit_iff]; exact hp.not_isUnit
      omega
    calc _ ≤ ({J | J ∣ a} ∪ (fun J => p * J) '' {J | J ∣ a}).ncard := Set.ncard_le_ncard hsub hfin2
      _ ≤ {J | J ∣ a}.ncard + ((fun J => p * J) '' {J | J ∣ a}).ncard := Set.ncard_union_le _ _
      _ ≤ {J | J ∣ a}.ncard + {J | J ∣ a}.ncard := by
          exact Nat.add_le_add_left (Set.ncard_image_le hfin) _
      _ = 2 * {J | J ∣ a}.ncard := by ring
      _ ≤ Ideal.absNorm p * Ideal.absNorm a := Nat.mul_le_mul hp2 hle
      _ = _ := (map_mul _ _ _).symm

section unfold
variable {G X : Type} [Group G] [MulAction G X]
open MulAction

/- English proof (translation)
Rewrite using `[← index_stabilizer K z, Subgroup.relIndex]`. Use `congr 1`.
-/
lemma relIndex_eq_ncard (K : Subgroup G) (z : X) :
    (stabilizer G z).relIndex K = (orbit K z).ncard := by
  rw [← index_stabilizer K z, Subgroup.relIndex]
  congr 1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, rfl⟩`. Conclude with `⟨k.1, k.2, rfl⟩`. Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨⟨k, hk⟩, rfl⟩`.
-/
lemma mem_orbit_sub (K : Subgroup G) (z w : X) : w ∈ orbit K z ↔ ∃ k ∈ K, k • z = w := by
  constructor
  · rintro ⟨k, rfl⟩; exact ⟨k.1, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hk⟩, rfl⟩

/- English proof (translation)
Establish `: orbit (stabilizer G y) (g⁻¹ • x) = (fun w => g⁻¹ • w) '' orbit (stabilizer G (g • y)) x`. Use extensionality with `w`. Simplify using `only [Set.mem_image, mem_orbit_sub, mem_stabilizer_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`.

Use `⟨(g * k * g⁻¹) • x, ⟨g * k * g⁻¹, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `[mul_smul, hk]`. Simplify using `[mul_smul]`. Introduce and unpack `⟨_, ⟨k, hk, rfl⟩, rfl⟩`. Use `⟨g⁻¹ * k * g, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `[mul_smul, hk]`. Simplify using `[mul_smul]`. Rewrite using `[this, Set.ncard_image_of_injective _ (MulAction.injective g⁻¹)]`.
-/
lemma ncard_conj (g : G) (x y : X) :
    (orbit (stabilizer G (g • y)) x).ncard = (orbit (stabilizer G y) (g⁻¹ • x)).ncard := by
  have : orbit (stabilizer G y) (g⁻¹ • x) = (fun w => g⁻¹ • w) '' orbit (stabilizer G (g • y)) x := by
    ext w
    simp only [Set.mem_image, mem_orbit_sub, mem_stabilizer_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨(g * k * g⁻¹) • x, ⟨g * k * g⁻¹, ?_, rfl⟩, ?_⟩
      · simp [mul_smul, hk]
      · simp [mul_smul]
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨g⁻¹ * k * g, ?_, ?_⟩
      · simp [mul_smul, hk]
      · simp [mul_smul]
  rw [this, Set.ncard_image_of_injective _ (MulAction.injective g⁻¹)]

end unfold

/- English proof (translation)
Use `Finset.sum_congr rfl fun z hz => ?_` and prove the remaining obligations. Take `⟨z0, hz0, hR0⟩` from `h1 z hz`. Establish `hpos : 0 < (B.filter (R z)).card` using `Finset.card_pos.2 ⟨z0, Finset.mem_filter.2 ⟨hz0, hR0⟩⟩`. Rewrite using `[Finset.sum_congr rfl (fun z' hz' => by`. Rewrite using `[← h2 z hz z' (Finset.mem_filter.1 hz').1 (Finset.mem_filter.1 hz').2] : ∀ z' ∈ B.filter (R z), F z / nb z' = F z / ((B.filter (R z)).card : ℝ)),`.

Use the proof step `Finset.sum_const, nsmul_eq_mul]`. Establish `: ((B.filter (R z)).card : ℝ) ≠ 0` using `by exact_mod_cast hpos.ne'`. Clear the denominators using the available nonvanishing facts.
-/
lemma fiber_sum {X : Type} (A B : Finset X) (R : X → X → Prop) [∀ z, DecidablePred (R z)] (F : X → ℝ)
    (nb : X → ℕ) (h1 : ∀ z ∈ A, ∃ z' ∈ B, R z z')
    (h2 : ∀ z ∈ A, ∀ z' ∈ B, R z z' → (B.filter (R z)).card = nb z') :
    ∑ z ∈ A, F z = ∑ z ∈ A, ∑ z' ∈ B.filter (R z), F z / nb z' := by
  refine Finset.sum_congr rfl fun z hz => ?_
  obtain ⟨z0, hz0, hR0⟩ := h1 z hz
  have hpos : 0 < (B.filter (R z)).card := Finset.card_pos.2 ⟨z0, Finset.mem_filter.2 ⟨hz0, hR0⟩⟩
  rw [Finset.sum_congr rfl (fun z' hz' => by
    rw [← h2 z hz z' (Finset.mem_filter.1 hz').1 (Finset.mem_filter.1 hz').2] :
      ∀ z' ∈ B.filter (R z), F z / nb z' = F z / ((B.filter (R z)).card : ℝ)),
    Finset.sum_const, nsmul_eq_mul]
  have : ((B.filter (R z)).card : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp

/- English proof (translation)
Introduce `G X _ _ μ m hμ hidx hsym hinv hfin x y`. Establish `hfA : (MulAction.orbit G y ∩ Function.support (m x)).Finite` using `(hfin x).subset fun z hz => hz.2`. Establish `hfB : (MulAction.orbit G x ∩ Function.support (m y)).Finite` using `(hfin y).subset fun z hz => hz.2`. Rewrite using `[finsum_mem_eq_sum _ hfA, finsum_mem_eq_sum _ hfB]`. Use `set A := hfA.toFinset with hA`.

Use `set B := hfB.toFinset with hB`. Establish `memA : ∀ z, z ∈ A ↔ z ∈ MulAction.orbit G y ∧ m x z ≠ 0` using `fun z => by simp [hA]`. Establish `memB : ∀ z, z ∈ B ↔ z ∈ MulAction.orbit G x ∧ m y z ≠ 0` using `fun z => by simp [hB]`. Set `R : X → X → Prop` to `fun z z' => ∃ g : G, g • y = z ∧ g⁻¹ • x = z'`. Establish `hm : ∀ z z', R z z' → m x z = m y z'`.

Introduce and unpack `_ _ ⟨g, rfl, rfl⟩`. Rewrite using `[hsym y, ← hinv g⁻¹ x (g • y)]`. Simplify using the standard rewrite rules. Establish `hRA : ∀ z z', R z z' → {w' | R z w'} = MulAction.orbit (MulAction.stabilizer G y) z'`. Introduce and unpack `_ _ ⟨g, rfl, rfl⟩`.

Use extensionality with `w'`. Simplify using `only [Set.mem_ofPred_eq, mem_orbit_sub, MulAction.mem_stabilizer_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g', h1, rfl⟩`. Use `⟨g'⁻¹ * g, ?_, by simp [mul_smul]⟩` and prove the remaining obligations.

Rewrite using `[mul_smul, ← h1]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨k, hk, rfl⟩`. Use `⟨g * k⁻¹, ?_, by simp [mul_smul]⟩` and prove the remaining obligations. Rewrite using `[mul_smul]`.

Use `congr 1`. Rewrite using `[inv_smul_eq_iff, hk]`. Establish `hRB : ∀ z z', R z z' → {w | R w z'} = MulAction.orbit (MulAction.stabilizer G x) z`. Introduce and unpack `_ _ ⟨g, rfl, rfl⟩`. Use extensionality with `w`.

Simplify using `only [Set.mem_ofPred_eq, mem_orbit_sub, MulAction.mem_stabilizer_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g', rfl, h1⟩`. Use `⟨g' * g⁻¹, ?_, by simp [mul_smul]⟩` and prove the remaining obligations. Rewrite using `[mul_smul, ← h1]`.

Simplify using the standard rewrite rules. Introduce and unpack `⟨k, hk, rfl⟩`. Use `⟨k * g, by simp [mul_smul], ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv_rev, mul_smul]`. Use `congr 1`.

Rewrite using `[inv_smul_eq_iff, hk]`. Establish `hbal : ∀ z z', R z z' → μ x * ((MulAction.orbit (MulAction.stabilizer G x) z).ncard : ℝ) = μ y * ((MulAction.orbit (MulAction.stabilizer G y) z').ncard : ℝ)`. Introduce and unpack `_ _ ⟨g, rfl, rfl⟩`. Use `hidx x (g • y)` as an intermediate fact. Rewrite `this` using `[relIndex_eq_ncard, relIndex_eq_ncard, hμ, ncard_conj]`.

Conclude with `this`. Establish `hAB : ∀ z z', R z z' → (z ∈ A ↔ z' ∈ B)`. Introduce `z z' hR`. Rewrite using `[memA, memB, hm z z' hR]`. Take `⟨g, rfl, rfl⟩` from `hR`.

Simplify using `[MulAction.mem_orbit]`. Establish `cA : ∀ z ∈ A, ∀ z' ∈ B, R z z' → (B.filter (R z)).card = (MulAction.orbit (MulAction.stabilizer G y) z').ncard`. Introduce `z hz z' _ hR`. Rewrite using `[← hRA z z' hR, ← Set.ncard_coe_finset]`. Use `congr 1`.

Use extensionality with `w'`. Simplify using `only [Finset.coe_filter, Set.mem_ofPred_eq]`. Conclude with `⟨fun h => h.2, fun h => ⟨(hAB z w' h).1 hz, h⟩⟩`. Establish `cB : ∀ z' ∈ B, ∀ z ∈ A, R z z' → (A.filter (fun w => R w z')).card = (MulAction.orbit (MulAction.stabilizer G x) z).ncard`. Introduce `z' hz' z _ hR`.

Rewrite using `[← hRB z z' hR, ← Set.ncard_coe_finset]`. Use `congr 1`. Use extensionality with `w`. Simplify using `only [Finset.coe_filter, Set.mem_ofPred_eq]`. Conclude with `⟨fun h => h.2, fun h => ⟨(hAB w z' h).2 hz', h⟩⟩`.

Establish `eA : ∀ z ∈ A, ∃ z' ∈ B, R z z'`. Introduce `z hz`. Take `⟨g, rfl⟩` from `((memA z).1 hz).1`. Establish `hR : R (g • y) (g⁻¹ • x)` using `⟨g, rfl, rfl⟩`. Conclude with `⟨_, (hAB _ _ hR).1 hz, hR⟩`.

Establish `eB : ∀ z' ∈ B, ∃ z ∈ A, R z z'`. Introduce `z' hz'`. Take `⟨g, rfl⟩` from `((memB z').1 hz').1`. Establish `hR : R (g⁻¹ • y) (g • x)` using `⟨g⁻¹, rfl, by simp⟩`. Conclude with `⟨_, (hAB _ _ hR).2 hz', hR⟩`.

Rewrite using `[Finset.mul_sum, Finset.mul_sum, fiber_sum A B R (fun z => μ x * m x z) _ eA cA, fiber_sum B A (fun z' z => R z z') (fun z' => μ y * m y z') _ eB cB]`. Repeatedly rewrite using `[Finset.sum_filter]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun z' hz' => Finset.sum_congr rfl fun z hz => ?_` and prove the remaining obligations. Use `split_ifs with hR`.

Establish `h1` using `hbal z z' hR`. Establish `n1 : ((MulAction.orbit (MulAction.stabilizer G y) z').ncard : ℝ) ≠ 0`. Rewrite using `[← cA z hz z' hz' hR]`. Establish `: 0 < (B.filter (R z)).card` using `Finset.card_pos.2 ⟨z', Finset.mem_filter.2 ⟨hz', hR⟩⟩`. Conclude with `this.ne'` after adjusting the coercions.

Establish `n2 : ((MulAction.orbit (MulAction.stabilizer G x) z).ncard : ℝ) ≠ 0`. Rewrite using `[← cB z' hz' z hz hR]`. Establish `: 0 < (A.filter (fun w => R w z')).card` using `Finset.card_pos.2 ⟨z, Finset.mem_filter.2 ⟨hz, hR⟩⟩`. Conclude with `this.ne'` after adjusting the coercions. Rewrite using `[hm z z' hR, div_eq_div_iff n1 n2]`.

Take the linear combination `(m y z') * h1`. Both sides reduce to the same expression.
-/
theorem unfolding_symmetric : UnfoldSym := by
  intro G X _ _ μ m hμ hidx hsym hinv hfin x y
  classical
  have hfA : (MulAction.orbit G y ∩ Function.support (m x)).Finite := (hfin x).subset fun z hz => hz.2
  have hfB : (MulAction.orbit G x ∩ Function.support (m y)).Finite := (hfin y).subset fun z hz => hz.2
  rw [finsum_mem_eq_sum _ hfA, finsum_mem_eq_sum _ hfB]
  set A := hfA.toFinset with hA
  set B := hfB.toFinset with hB
  have memA : ∀ z, z ∈ A ↔ z ∈ MulAction.orbit G y ∧ m x z ≠ 0 := fun z => by simp [hA]
  have memB : ∀ z, z ∈ B ↔ z ∈ MulAction.orbit G x ∧ m y z ≠ 0 := fun z => by simp [hB]
  let R : X → X → Prop := fun z z' => ∃ g : G, g • y = z ∧ g⁻¹ • x = z'
  have hm : ∀ z z', R z z' → m x z = m y z' := by
    rintro _ _ ⟨g, rfl, rfl⟩
    rw [hsym y, ← hinv g⁻¹ x (g • y)]; simp
  have hRA : ∀ z z', R z z' → {w' | R z w'} = MulAction.orbit (MulAction.stabilizer G y) z' := by
    rintro _ _ ⟨g, rfl, rfl⟩
    ext w'
    simp only [Set.mem_ofPred_eq, mem_orbit_sub, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨g', h1, rfl⟩
      refine ⟨g'⁻¹ * g, ?_, by simp [mul_smul]⟩
      rw [mul_smul, ← h1]; simp
    · rintro ⟨k, hk, rfl⟩
      refine ⟨g * k⁻¹, ?_, by simp [mul_smul]⟩
      rw [mul_smul]
      congr 1
      rw [inv_smul_eq_iff, hk]
  have hRB : ∀ z z', R z z' → {w | R w z'} = MulAction.orbit (MulAction.stabilizer G x) z := by
    rintro _ _ ⟨g, rfl, rfl⟩
    ext w
    simp only [Set.mem_ofPred_eq, mem_orbit_sub, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨g', rfl, h1⟩
      refine ⟨g' * g⁻¹, ?_, by simp [mul_smul]⟩
      rw [mul_smul, ← h1]; simp
    · rintro ⟨k, hk, rfl⟩
      refine ⟨k * g, by simp [mul_smul], ?_⟩
      rw [mul_inv_rev, mul_smul]
      congr 1
      rw [inv_smul_eq_iff, hk]
  have hbal : ∀ z z', R z z' →
      μ x * ((MulAction.orbit (MulAction.stabilizer G x) z).ncard : ℝ)
        = μ y * ((MulAction.orbit (MulAction.stabilizer G y) z').ncard : ℝ) := by
    rintro _ _ ⟨g, rfl, rfl⟩
    have := hidx x (g • y)
    rw [relIndex_eq_ncard, relIndex_eq_ncard, hμ, ncard_conj] at this
    exact this
  have hAB : ∀ z z', R z z' → (z ∈ A ↔ z' ∈ B) := by
    intro z z' hR
    rw [memA, memB, hm z z' hR]
    obtain ⟨g, rfl, rfl⟩ := hR
    simp [MulAction.mem_orbit]
  have cA : ∀ z ∈ A, ∀ z' ∈ B, R z z' →
      (B.filter (R z)).card = (MulAction.orbit (MulAction.stabilizer G y) z').ncard := by
    intro z hz z' _ hR
    rw [← hRA z z' hR, ← Set.ncard_coe_finset]
    congr 1
    ext w'
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨(hAB z w' h).1 hz, h⟩⟩
  have cB : ∀ z' ∈ B, ∀ z ∈ A, R z z' →
      (A.filter (fun w => R w z')).card = (MulAction.orbit (MulAction.stabilizer G x) z).ncard := by
    intro z' hz' z _ hR
    rw [← hRB z z' hR, ← Set.ncard_coe_finset]
    congr 1
    ext w
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨(hAB w z' h).2 hz', h⟩⟩
  have eA : ∀ z ∈ A, ∃ z' ∈ B, R z z' := by
    intro z hz
    obtain ⟨g, rfl⟩ := ((memA z).1 hz).1
    have hR : R (g • y) (g⁻¹ • x) := ⟨g, rfl, rfl⟩
    exact ⟨_, (hAB _ _ hR).1 hz, hR⟩
  have eB : ∀ z' ∈ B, ∃ z ∈ A, R z z' := by
    intro z' hz'
    obtain ⟨g, rfl⟩ := ((memB z').1 hz').1
    have hR : R (g⁻¹ • y) (g • x) := ⟨g⁻¹, rfl, by simp⟩
    exact ⟨_, (hAB _ _ hR).2 hz', hR⟩
  rw [Finset.mul_sum, Finset.mul_sum,
    fiber_sum A B R (fun z => μ x * m x z) _ eA cA,
    fiber_sum B A (fun z' z => R z z') (fun z' => μ y * m y z') _ eB cB]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z' hz' => Finset.sum_congr rfl fun z hz => ?_
  split_ifs with hR
  · have h1 := hbal z z' hR
    have n1 : ((MulAction.orbit (MulAction.stabilizer G y) z').ncard : ℝ) ≠ 0 := by
      rw [← cA z hz z' hz' hR]
      have : 0 < (B.filter (R z)).card := Finset.card_pos.2 ⟨z', Finset.mem_filter.2 ⟨hz', hR⟩⟩
      exact_mod_cast this.ne'
    have n2 : ((MulAction.orbit (MulAction.stabilizer G x) z).ncard : ℝ) ≠ 0 := by
      rw [← cB z' hz' z hz hR]
      have : 0 < (A.filter (fun w => R w z')).card := Finset.card_pos.2 ⟨z, Finset.mem_filter.2 ⟨hz, hR⟩⟩
      exact_mod_cast this.ne'
    rw [hm z z' hR, div_eq_div_iff n1 n2]
    linear_combination (m y z') * h1
  · rfl

section dualcap
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]

/- English proof (translation)
Use `hU.free` as an intermediate fact. Establish `: Module.Finite o O` using `Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)`. Set `b` to `Module.Free.chooseBasis o O`. Rewrite using `[← b.sum_repr c]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Take `⟨bi, hbi⟩` from `hU.tr_perfect (b.coord i)`. Establish `h1` using `hbi c`. Rewrite `h1` using `[mul_comm c (star bi), hc (star bi), Module.Basis.coord_apply]`. Rewrite using `[Algebra.smul_def, h1, zero_mul]`.
-/
lemma unram_uniq (hU : Unram o O) (c : O) (hc : ∀ a : O, a * c + star (a * c) = 0) : c = 0 := by
  classical
  have := hU.free
  have : Module.Finite o O := Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)
  let b := Module.Free.chooseBasis o O
  rw [← b.sum_repr c]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨bi, hbi⟩ := hU.tr_perfect (b.coord i)
  have h1 := hbi c
  rw [mul_comm c (star bi), hc (star bi), Module.Basis.coord_apply] at h1
  rw [Algebra.smul_def, h1, zero_mul]

/- English proof (translation)
Use `hU.free` as an intermediate fact. Establish `: Module.Finite o O` using `Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)`. Set `b` to `Module.Free.chooseBasis o O`. Establish `hne : Nonempty (Module.Free.ChooseBasisIndex o O)`. Assume the negation of the conclusion as `hcon`.

Rewrite `hcon` using `[not_nonempty_iff]`. Use `Module.finrank_eq_card_basis b` as an intermediate fact. Rewrite `this` using `[hU.rank2, Fintype.card_eq_zero]`. Use linear arithmetic over natural numbers and integers. Take `⟨i0⟩` from `hne`.

Distinguish the cases in `hex : ∃ i, IsUnit (b.repr 1 i)`. Take `⟨i, u, hu⟩` from `hex`. Use `⟨((u⁻¹ : oˣ) : o) • b.coord i, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, Module.Basis.coord_apply, ← hu, smul_eq_mul, Units.inv_mul]`. Use `exfalso push Not at hex`.

Establish `h1 : b i0 = ∑ j, b.repr 1 j • (b j * b i0)` using `by conv_lhs => rw [← one_mul (b i0), ← b.sum_repr 1, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [smul_mul_assoc]`. Establish `h2 : (1 : o) = ∑ j, b.repr 1 j * b.repr (b j * b i0) i0`. Use `congrArg (fun z => b.repr z i0) h1` as an intermediate fact. Simplify `this` using `[map_sum, Finsupp.finsetSum_apply]`.

Establish `h3 : (1 : o) ∈ IsLocalRing.maximalIdeal o`. Rewrite using `[h2]`. Conclude with `Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hex j))`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal o).ne_top ((Ideal.eq_top_iff_one _).2 h3)`.
-/
lemma unram_one (hU : Unram o O) : ∃ l : O →ₗ[o] o, l 1 = 1 := by
  classical
  have := hU.free
  have : Module.Finite o O := Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)
  let b := Module.Free.chooseBasis o O
  have hne : Nonempty (Module.Free.ChooseBasisIndex o O) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have := Module.finrank_eq_card_basis b
    rw [hU.rank2, Fintype.card_eq_zero] at this
    omega
  obtain ⟨i0⟩ := hne
  by_cases hex : ∃ i, IsUnit (b.repr 1 i)
  · obtain ⟨i, u, hu⟩ := hex
    refine ⟨((u⁻¹ : oˣ) : o) • b.coord i, ?_⟩
    rw [LinearMap.smul_apply, Module.Basis.coord_apply, ← hu, smul_eq_mul, Units.inv_mul]
  · exfalso
    push Not at hex
    have h1 : b i0 = ∑ j, b.repr 1 j • (b j * b i0) := by
      conv_lhs => rw [← one_mul (b i0), ← b.sum_repr 1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_mul_assoc]
    have h2 : (1 : o) = ∑ j, b.repr 1 j * b.repr (b j * b i0) i0 := by
      have := congrArg (fun z => b.repr z i0) h1
      simpa [map_sum, Finsupp.finsetSum_apply] using this
    have h3 : (1 : o) ∈ IsLocalRing.maximalIdeal o := by
      rw [h2]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hex j))
    exact (IsLocalRing.maximalIdeal.isMaximal o).ne_top ((Ideal.eq_top_iff_one _).2 h3)

/- English proof (translation)
Take `⟨l, hl⟩` from `unram_one hU`. Take `⟨b0, hb0⟩` from `hU.tr_perfect l`. Set `sl : O →ₗ[o] O` to `{ toFun := star map_add' := star_add map_smul' := fun c a => by`. Simplify using `only [Algebra.smul_def, star_mul', hU.star_o, RingHom.id_apply] }`. Establish `h1 : star b0 + b0 = 1`.

Use `hb0 1` as an intermediate fact. Rewrite `this` using `[hl, map_one, one_mul, star_star]`. Conclude with `this.symm`. Use `⟨l + l ∘ₗ sl, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.add_apply, LinearMap.comp_apply, map_add, hb0, hb0]`.

Express the relevant statement in the definitionally equal form `a * star b0 + star (a * star b0) + (star a * star b0 + star (star a * star b0)) = _`. Simplify using `only [star_mul', star_star]`. Take the linear combination `(a + star a) * h1`.
-/
lemma unram_trace (hU : Unram o O) : ∃ T : O →ₗ[o] o, ∀ a, algebraMap o O (T a) = a + star a := by
  obtain ⟨l, hl⟩ := unram_one hU
  obtain ⟨b0, hb0⟩ := hU.tr_perfect l
  let sl : O →ₗ[o] O :=
    { toFun := star
      map_add' := star_add
      map_smul' := fun c a => by
        simp only [Algebra.smul_def, star_mul', hU.star_o, RingHom.id_apply] }
  have h1 : star b0 + b0 = 1 := by
    have := hb0 1
    rw [hl, map_one, one_mul, star_star] at this
    exact this.symm
  refine ⟨l + l ∘ₗ sl, fun a => ?_⟩
  rw [LinearMap.add_apply, LinearMap.comp_apply, map_add, hb0, hb0]
  change a * star b0 + star (a * star b0) + (star a * star b0 + star (star a * star b0)) = _
  simp only [star_mul', star_star]
  linear_combination (a + star a) * h1

end dualcap

/- English proof (translation)
Introduce `o O abelian₂ _ _ _ _ _ _ _ _ _ _ h hU hSD S hS φ`. Take `⟨T, hT⟩` from `unram_trace hU`. Establish `hUq` using `unram_uniq hU`. Use `hU.free` as an intermediate fact. Establish `: Module.Finite o O` using `Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)`.

Set `: Module o abelian₂` to `Module.compHom abelian₂ (algebraMap o O)`. Establish `: IsScalarTower o O abelian₂` using `IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Establish `: Module.Finite o abelian₂` using `Module.Finite.trans O abelian₂`. Set `S' : Submodule o abelian₂` to `S.restrictScalars o`. Establish `: Module.IsTorsionFree o (abelian₂ ⧸ S')`.

Apply `Module.IsTorsionFree.of_smul_eq_zero` to reduce the goal to its premises. Introduce `r m hrm`. Distinguish the cases in `hr : r = 0`. Conclude with `Or.inl hr`. Use `right`.

Take `⟨v, rfl⟩` from `S'.mkQ_surjective m`. Rewrite `hrm` using `[← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hS r v hr hrm`. Take `⟨σ, hσ⟩` from `Module.projective_lifting_property S'.mkQ LinearMap.id S'.mkQ_surjective`.

Set `ρ : abelian₂ →ₗ[o] abelian₂` to `LinearMap.id - σ ∘ₗ S'.mkQ`. Establish `hρmem : ∀ v, ρ v ∈ S`. Introduce `v`. Establish `: S'.mkQ (ρ v) = 0`. Establish `h1` using `LinearMap.congr_fun hσ (S'.mkQ v)`.

Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at h1`. Simplify using `only [ρ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]`. Rewrite `this` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `this`. Establish `hρfix : ∀ v ∈ S, ρ v = v`.

Introduce `v hv`. Establish `: S'.mkQ v = 0` using `by rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hv`. Simplify using `only [ρ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, this, map_zero, sub_zero]`. Set `Λ : abelian₂ →ₗ[o] o` to `{ toFun := fun v => T (φ ⟨ρ v, hρmem v⟩) map_add' := fun v w => by`. Establish `: (⟨ρ (v + w), hρmem (v + w)⟩ : S) = ⟨ρ v, hρmem v⟩ + ⟨ρ w, hρmem w⟩` using `Subtype.ext (map_add ρ v w)`.

Rewrite using `[this, map_add, map_add]`. Use the proof step `map_smul' := fun c v => by`. Establish `: (⟨ρ (c • v), hρmem (c • v)⟩ : S) = algebraMap o O c • ⟨ρ v, hρmem v⟩` using `Subtype.ext (map_smul ρ c v)`. Rewrite using `[this, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul, RingHom.id_apply] }`. Establish `hΛ : ∀ v, Λ v = T (φ ⟨ρ v, hρmem v⟩)` using `fun v => rfl`.

Establish `hex : ∀ v : abelian₂, ∃ c : O, ∀ a : O, algebraMap o O (Λ (a • v)) = a * c + star (a * c)`. Introduce `v`. Take `⟨bv, hbv⟩` from `hU.tr_perfect (Λ ∘ₗ (LinearMap.toSpanSingleton O abelian₂ v).restrictScalars o)`. Conclude with `⟨star bv, fun a => hbv a⟩`. Use `choose Φ hΦ using hex`.

Set `Φl : abelian₂ →ₗ[O] O` to `{ toFun := Φ map_add' := fun v w => by`. Rewrite using `[← sub_eq_zero]`. Apply `hUq` to reduce the goal to its premises. Introduce `a`. Establish `h1` using `hΦ (v + w) a`.

Rewrite `h1` using `[smul_add, map_add, map_add, hΦ v a, hΦ w a]`. Simplify using `only [mul_sub, mul_add, star_sub, star_add]`. Take the linear combination `-h1`. Use the proof step `map_smul' := fun r v => by`. Rewrite using `[← sub_eq_zero]`.

Apply `hUq` to reduce the goal to its premises. Introduce `a`. Establish `h1` using `hΦ (r • v) a`. Rewrite `h1` using `[smul_smul, hΦ v (a * r)]`. Simplify using `only [RingHom.id_apply, smul_eq_mul, mul_sub, star_sub, ← mul_assoc]`.

Take the linear combination `-h1 }`. Take `⟨w, hw⟩` from `hSD.2 Φl`. Use `⟨w, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[← hw]`. Express the relevant statement in the definitionally equal form `φ v = Φ v`.

Use `symm`. Rewrite using `[← sub_eq_zero]`. Apply `hUq` to reduce the goal to its premises. Introduce `a`. Establish `h1` using `hΦ v a`.

Establish `h2 : (⟨ρ (a • (v : abelian₂)), hρmem _⟩ : S) = a • v` using `Subtype.ext (hρfix _ (S.smul_mem a v.2))`. Rewrite `h1` using `[hΛ, h2, map_smul, smul_eq_mul, hT]`. Simplify using `only [mul_sub, star_sub]`. Take the linear combination `-h1`.
-/
theorem dual_capacity_formula : DualCap := by
  intro o O abelian₂ _ _ _ _ _ _ _ _ _ _ h hU hSD S hS φ
  classical
  obtain ⟨T, hT⟩ := unram_trace hU
  have hUq := unram_uniq hU
  have := hU.free
  have : Module.Finite o O := Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)
  let : Module o abelian₂ := Module.compHom abelian₂ (algebraMap o O)
  have : IsScalarTower o O abelian₂ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite o abelian₂ := Module.Finite.trans O abelian₂
  let S' : Submodule o abelian₂ := S.restrictScalars o
  have : Module.IsTorsionFree o (abelian₂ ⧸ S') := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro r m hrm
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      obtain ⟨v, rfl⟩ := S'.mkQ_surjective m
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hrm
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hS r v hr hrm
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property S'.mkQ LinearMap.id S'.mkQ_surjective
  let ρ : abelian₂ →ₗ[o] abelian₂ := LinearMap.id - σ ∘ₗ S'.mkQ
  have hρmem : ∀ v, ρ v ∈ S := by
    intro v
    have : S'.mkQ (ρ v) = 0 := by
      have h1 := LinearMap.congr_fun hσ (S'.mkQ v)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
      simp only [ρ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this
  have hρfix : ∀ v ∈ S, ρ v = v := by
    intro v hv
    have : S'.mkQ v = 0 := by rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hv
    simp only [ρ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, this, map_zero, sub_zero]
  let Λ : abelian₂ →ₗ[o] o :=
    { toFun := fun v => T (φ ⟨ρ v, hρmem v⟩)
      map_add' := fun v w => by
        have : (⟨ρ (v + w), hρmem (v + w)⟩ : S) = ⟨ρ v, hρmem v⟩ + ⟨ρ w, hρmem w⟩ :=
          Subtype.ext (map_add ρ v w)
        rw [this, map_add, map_add]
      map_smul' := fun c v => by
        have : (⟨ρ (c • v), hρmem (c • v)⟩ : S) = algebraMap o O c • ⟨ρ v, hρmem v⟩ :=
          Subtype.ext (map_smul ρ c v)
        rw [this, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul, RingHom.id_apply] }
  have hΛ : ∀ v, Λ v = T (φ ⟨ρ v, hρmem v⟩) := fun v => rfl
  have hex : ∀ v : abelian₂, ∃ c : O, ∀ a : O, algebraMap o O (Λ (a • v)) = a * c + star (a * c) := by
    intro v
    obtain ⟨bv, hbv⟩ := hU.tr_perfect (Λ ∘ₗ (LinearMap.toSpanSingleton O abelian₂ v).restrictScalars o)
    exact ⟨star bv, fun a => hbv a⟩
  choose Φ hΦ using hex
  let Φl : abelian₂ →ₗ[O] O :=
    { toFun := Φ
      map_add' := fun v w => by
        rw [← sub_eq_zero]
        apply hUq
        intro a
        have h1 := hΦ (v + w) a
        rw [smul_add, map_add, map_add, hΦ v a, hΦ w a] at h1
        simp only [mul_sub, mul_add, star_sub, star_add]
        linear_combination -h1
      map_smul' := fun r v => by
        rw [← sub_eq_zero]
        apply hUq
        intro a
        have h1 := hΦ (r • v) a
        rw [smul_smul, hΦ v (a * r)] at h1
        simp only [RingHom.id_apply, smul_eq_mul, mul_sub, star_sub, ← mul_assoc]
        linear_combination -h1 }
  obtain ⟨w, hw⟩ := hSD.2 Φl
  refine ⟨w, fun v => ?_⟩
  rw [← hw]
  change φ v = Φ v
  symm
  rw [← sub_eq_zero]
  apply hUq
  intro a
  have h1 := hΦ v a
  have h2 : (⟨ρ (a • (v : abelian₂)), hρmem _⟩ : S) = a • v := Subtype.ext (hρfix _ (S.smul_mem a v.2))
  rw [hΛ, h2, map_smul, smul_eq_mul, hT] at h1
  simp only [mul_sub, star_sub]
  linear_combination -h1

/- English proof (translation)
Establish `hdiag : ∀ j, ∃ s ∈ O, s + star s = γ j j` using `fun j => htr _ (hO j j) (hγ j j)`. Use `choose s hs hss using hdiag`. Use `⟨fun j l => if j < l then γ j l else if j = l then s j else 0, fun j l => ?_, fun j k => ?_⟩` and prove the remaining obligations. Simplify using `only split_ifs exacts [hO j l, hs j, O.zero_mem]`. Break down `lt_trichotomy j k with hjk | hjk | hjk` into its components or cases.

Simplify using `[hjk, hjk.not_gt, hjk.ne']`. Substitute `hjk` using the available equality. Simplify using `[hss]`. Simplify using `[hjk, hjk.not_gt, hjk.ne', hγ]`.
-/
lemma herm_split {E : Type} [CommRing E] [StarRing E] (O : Subring E)
    (htr : ∀ c ∈ O, star c = c → ∃ s ∈ O, s + star s = c) (r : ℕ) (γ : Fin r → Fin r → E)
    (hO : ∀ j k, γ j k ∈ O) (hγ : ∀ j k, star (γ j k) = γ k j) :
    ∃ c : Fin r → Fin r → E, (∀ j k, c j k ∈ O) ∧ ∀ j k, c j k + star (c k j) = γ j k := by
  have hdiag : ∀ j, ∃ s ∈ O, s + star s = γ j j := fun j => htr _ (hO j j) (hγ j j)
  choose s hs hss using hdiag
  refine ⟨fun j l => if j < l then γ j l else if j = l then s j else 0, fun j l => ?_, fun j k => ?_⟩
  · dsimp only
    split_ifs
    exacts [hO j l, hs j, O.zero_mem]
  · rcases lt_trichotomy j k with hjk | hjk | hjk
    · simp [hjk, hjk.not_gt, hjk.ne']
    · subst hjk; simp [hss]
    · simp [hjk, hjk.not_gt, hjk.ne', hγ]

section sametrace
variable {E : Type} [CommRing E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  (h : V →ₗ[E] V →ₗ⋆[E] E) {r : ℕ} (e : Fin r → V)

def shear (t : Fin r → V) : V →ₗ[E] V where
  toFun v := v + ∑ j, h v (e j) • t j
  map_add' v w := by
    simp only [map_add, LinearMap.add_apply, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c v := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add,
      Finset.smul_sum]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma shear_apply (t : Fin r → V) (v : V) : shear h e t v = v + ∑ j, h v (e j) • t j := rfl

/- English proof (translation)
Simplify using `[shear_apply, map_sum, LinearMap.sum_apply, ht]`.
-/
lemma shear_pair (t : Fin r → V) (ht : ∀ j i, h (t j) (e i) = 0) (v : V) (i : Fin r) :
    h (shear h e t v) (e i) = h v (e i) := by
  simp [shear_apply, map_sum, LinearMap.sum_apply, ht]

/- English proof (translation)
Rewrite using `[shear_apply]`. Simplify using `only [shear_pair h e t ht]`. Rewrite using `[shear_apply]`. Simplify using the standard rewrite rules.
-/
lemma shear_inv (t : Fin r → V) (ht : ∀ j i, h (t j) (e i) = 0) (v : V) :
    shear h e (fun j => - t j) (shear h e t v) = v := by
  rw [shear_apply]
  simp only [shear_pair h e t ht]
  rw [shear_apply]
  simp

end sametrace

/- English proof (translation)
Introduce `E _ _ V _ _ h O La Lb r e y yb hH htr hLa hLb hIa hIb he heLa hcap hy hyb hd hdb hD`. Establish `heLb : ∀ i, e i ∈ Lb` using `fun i => (hcap _ (fun k => he i k)).1 (heLa i)`. Establish `hdj : ∀ j, ∃ l ∈ La, (∀ i, h l (e i) = 0) ∧ ∃ c : Fin r → E, yb j - y j = l + ∑ i, c i • e i`. Introduce `j`. Apply `hD` to reduce the goal to its premises.

Introduce `i`. Rewrite using `[map_sub, LinearMap.sub_apply, hd, hdb, sub_self]`. Introduce `v hv hv0`. Rewrite using `[map_sub]`. Conclude with `O.sub_mem (hIb _ ((hcap v hv0).1 hv) _ (hyb j)) (hIa _ hv _ (hy j))`.

Use `choose l hl hl0 c hc using hdj`. Establish `tE : ∀ (a : Fin r → E) i, h (∑ k, a k • e k) (e i) = 0`. Introduce `a i`. Simplify using `[map_sum, LinearMap.sum_apply, he]`. Establish `Et : ∀ (a : Fin r → E) (v : V), h v (∑ k, a k • e k) = ∑ k, star (a k) * h v (e k)`.

Introduce `a v`. Simplify using `[map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply]`. Establish `tv : ∀ (a : Fin r → E) (w : V), h (∑ k, a k • e k) w = ∑ k, a k * star (h w (e k))`. Introduce `a w`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]`.

Conclude with `Finset.sum_congr rfl fun k _ => by rw [hH w (e k)]`. Establish `tt : ∀ (a b : Fin r → E), h (∑ k, a k • e k) (∑ k, b k • e k) = 0`. Introduce `a b`. Rewrite using `[Et]`. Conclude with `Finset.sum_eq_zero fun k _ => by rw [tE, mul_zero]`.

Establish `pairing : ∀ (a : Fin r → Fin r → E) j k, h (y j + ∑ i, a j i • e i) (y k + ∑ i, a k i • e i) = h (y j) (y k) + (a j k + star (a k j))`. Introduce `a j k`. Rewrite using `[map_add (h _), map_add h, LinearMap.add_apply, LinearMap.add_apply, tt, Et, tv]`. Simplify using `only [hd, apply_ite (star : E → E), star_one, star_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hz : ∀ j, y j + ∑ i, c j i • e i ∈ Lb`. Introduce `j`. Establish `: y j + ∑ i, c j i • e i = yb j - l j`. Use `hc j` as an intermediate fact. Rewrite `this` using `[sub_eq_iff_eq_add]`.

Rewrite using `[this]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `Lb.sub_mem (hyb j) ((hcap _ (hl0 j)).1 (hl j))`. Take `⟨c', hc'O, hc'⟩` from `herm_split O htr r (fun j k => c j k + star (c k j)) (fun j k => by`.

Establish `h1` using `pairing c j k`. Establish `h2 : c j k + star (c k j) = h (y j + ∑ i, c j i • e i) (y k + ∑ i, c k i • e i) - h (y j) (y k)`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`.

Conclude with `O.sub_mem (hIb _ (hz j) _ (hz k)) (hIa _ (hy j) _ (hy k)))`. Use the proof step `(fun j k => by simp [add_comm])`. Take `⟨a, ha⟩ : ∃ a : Fin r → Fin r → E, a = fun j i => c j i - c' j i` from `⟨_, rfl⟩`. Establish `hskew : ∀ j k, a j k + star (a k j) = 0`. Introduce `j k`.

Simplify using `only [ha, star_sub]`. Take the linear combination `-(hc' j k)`. Take `⟨t, ht⟩ : ∃ t : Fin r → V, t = fun j => ∑ i, a j i • e i` from `⟨_, rfl⟩`. Establish `htE : ∀ j i, h (t j) (e i) = 0` using `fun j i => by rw [ht]; exact tE _ i`. Establish `hntE : ∀ j i, h ((fun j => - t j) j) (e i) = 0` using `fun j i => by simp [htE]`.

Establish `hzz : ∀ j, y j + t j ∈ Lb`. Introduce `j`. Establish `: y j + t j = (y j + ∑ i, c j i • e i) - ∑ i, c' j i • e i`. Simplify using `only [ht, ha, sub_smul, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws.

Rewrite using `[this]`. Conclude with `Lb.sub_mem (hz j) (Lb.sum_mem fun i _ => hLb _ (hc'O j i) _ (heLb i))`. Set `n : V ≃ₗ[E] V` to `LinearEquiv.ofLinearMap (shear h e t) (shear h e (fun j => - t j)) (by`. Use extensionality with `v`. Use `shear_inv h e (fun j => - t j) hntE v` as an intermediate fact.

Simplify using `using this)`. Use the proof step `(by ext v; exact shear_inv h e t htE v)`. Establish `hn : ∀ v, n v = v + ∑ j, h v (e j) • t j` using `fun v => rfl`. Use `⟨n, fun v w => ?_, fun v hv => ?_, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hn, hn]`.

Simplify using `only [map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_apply]`. Establish `h3 : ∀ j k, h (t j) (t k) = 0` using `fun j k => by`. Simplify using `only [ht]`. Conclude with `tt _ _`. Simplify using `only [h3, mul_zero, Finset.sum_const_zero, add_zero]`.

Simplify using `only [ht, Et, tv, Finset.mul_sum]`. Rewrite using `[add_assoc, add_eq_left, Finset.sum_comm, ← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Take the linear combination `(h v (e i) * star (h w (e j))) * hskew i j`. Rewrite using `[hn]`. Simplify using `[hv]`. Rewrite using `[hn]`. Establish `h0 : ∀ i, h (v - ∑ j, h v (e j) • y j) (e i) = 0`.

Introduce `i`. Simplify using `[map_sum, LinearMap.sum_apply, hd]`. Establish `hm : v - ∑ j, h v (e j) • y j ∈ La` using `La.sub_mem hv (La.sum_mem fun j _ => hLa _ (hIa _ hv _ (heLa j)) _ (hy j))`. Establish `: v + ∑ j, h v (e j) • t j = (v - ∑ j, h v (e j) • y j) + ∑ j, h v (e j) • (y j + t j)`. Simplify using `only [smul_add, Finset.sum_add_distrib]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `Lb.add_mem ((hcap _ h0).1 hm) (Lb.sum_mem fun j _ => hLb _ (hIa _ hv _ (heLa j)) _ (hzz j))`. Establish `hp : ∀ i, h (n v) (e i) = h v (e i)` using `fun i => shear_pair h e t htE v i`. Establish `hpO : ∀ i, h v (e i) ∈ O` using `fun i => by rw [← hp]; exact hIb _ hv _ (heLb i)`.

Establish `h0 : ∀ i, h (n v - ∑ j, h v (e j) • (y j + t j)) (e i) = 0`. Introduce `i`. Simplify using `[map_sum, LinearMap.sum_apply, hd, hp, htE]`. Establish `hm : n v - ∑ j, h v (e j) • (y j + t j) ∈ Lb` using `Lb.sub_mem hv (Lb.sum_mem fun j _ => hLb _ (hpO j) _ (hzz j))`. Establish `: v = (n v - ∑ j, h v (e j) • (y j + t j)) + ∑ j, h v (e j) • y j`.

Rewrite using `[hn]`. Simplify using `only [smul_add, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `La.add_mem ((hcap _ h0).2 hm) (La.sum_mem fun j _ => hLa _ (hpO j) _ (hy j))`.
-/
theorem same_trace_count : SameTrace := by
  intro E _ _ V _ _ h O La Lb r e y yb hH htr hLa hLb hIa hIb he heLa hcap hy hyb hd hdb hD
  have heLb : ∀ i, e i ∈ Lb := fun i => (hcap _ (fun k => he i k)).1 (heLa i)
  have hdj : ∀ j, ∃ l ∈ La, (∀ i, h l (e i) = 0) ∧ ∃ c : Fin r → E, yb j - y j = l + ∑ i, c i • e i := by
    intro j
    apply hD
    · intro i; rw [map_sub, LinearMap.sub_apply, hd, hdb, sub_self]
    · intro v hv hv0
      rw [map_sub]
      exact O.sub_mem (hIb _ ((hcap v hv0).1 hv) _ (hyb j)) (hIa _ hv _ (hy j))
  choose l hl hl0 c hc using hdj
  have tE : ∀ (a : Fin r → E) i, h (∑ k, a k • e k) (e i) = 0 := by
    intro a i; simp [map_sum, LinearMap.sum_apply, he]
  have Et : ∀ (a : Fin r → E) (v : V), h v (∑ k, a k • e k) = ∑ k, star (a k) * h v (e k) := by
    intro a v; simp [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply]
  have tv : ∀ (a : Fin r → E) (w : V), h (∑ k, a k • e k) w = ∑ k, a k * star (h w (e k)) := by
    intro a w
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [hH w (e k)]
  have tt : ∀ (a b : Fin r → E), h (∑ k, a k • e k) (∑ k, b k • e k) = 0 := by
    intro a b
    rw [Et]
    exact Finset.sum_eq_zero fun k _ => by rw [tE, mul_zero]
  have pairing : ∀ (a : Fin r → Fin r → E) j k,
      h (y j + ∑ i, a j i • e i) (y k + ∑ i, a k i • e i) = h (y j) (y k) + (a j k + star (a k j)) := by
    intro a j k
    rw [map_add (h _), map_add h, LinearMap.add_apply, LinearMap.add_apply, tt, Et, tv]
    simp only [hd, apply_ite (star : E → E), star_one, star_zero, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hz : ∀ j, y j + ∑ i, c j i • e i ∈ Lb := by
    intro j
    have : y j + ∑ i, c j i • e i = yb j - l j := by
      have := hc j
      rw [sub_eq_iff_eq_add] at this
      rw [this]; abel
    rw [this]
    exact Lb.sub_mem (hyb j) ((hcap _ (hl0 j)).1 (hl j))
  obtain ⟨c', hc'O, hc'⟩ := herm_split O htr r (fun j k => c j k + star (c k j))
    (fun j k => by
      have h1 := pairing c j k
      have h2 : c j k + star (c k j) = h (y j + ∑ i, c j i • e i) (y k + ∑ i, c k i • e i) - h (y j) (y k) := by
        rw [h1]; ring
      rw [h2]
      exact O.sub_mem (hIb _ (hz j) _ (hz k)) (hIa _ (hy j) _ (hy k)))
    (fun j k => by simp [add_comm])
  obtain ⟨a, ha⟩ : ∃ a : Fin r → Fin r → E, a = fun j i => c j i - c' j i := ⟨_, rfl⟩
  have hskew : ∀ j k, a j k + star (a k j) = 0 := by
    intro j k
    simp only [ha, star_sub]
    linear_combination -(hc' j k)
  obtain ⟨t, ht⟩ : ∃ t : Fin r → V, t = fun j => ∑ i, a j i • e i := ⟨_, rfl⟩
  have htE : ∀ j i, h (t j) (e i) = 0 := fun j i => by rw [ht]; exact tE _ i
  have hntE : ∀ j i, h ((fun j => - t j) j) (e i) = 0 := fun j i => by simp [htE]
  have hzz : ∀ j, y j + t j ∈ Lb := by
    intro j
    have : y j + t j = (y j + ∑ i, c j i • e i) - ∑ i, c' j i • e i := by
      simp only [ht, ha, sub_smul, Finset.sum_sub_distrib]; abel
    rw [this]
    exact Lb.sub_mem (hz j) (Lb.sum_mem fun i _ => hLb _ (hc'O j i) _ (heLb i))
  let n : V ≃ₗ[E] V := LinearEquiv.ofLinearMap (shear h e t) (shear h e (fun j => - t j))
    (by
      ext v
      have := shear_inv h e (fun j => - t j) hntE v
      simpa using this)
    (by ext v; exact shear_inv h e t htE v)
  have hn : ∀ v, n v = v + ∑ j, h v (e j) • t j := fun v => rfl
  refine ⟨n, fun v w => ?_, fun v hv => ?_, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · rw [hn, hn]
    simp only [map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_apply]
    have h3 : ∀ j k, h (t j) (t k) = 0 := fun j k => by
      simp only [ht]; exact tt _ _
    simp only [h3, mul_zero, Finset.sum_const_zero, add_zero]
    simp only [ht, Et, tv, Finset.mul_sum]
    rw [add_assoc, add_eq_left, Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    linear_combination (h v (e i) * star (h w (e j))) * hskew i j
  · rw [hn]; simp [hv]
  · rw [hn]
    have h0 : ∀ i, h (v - ∑ j, h v (e j) • y j) (e i) = 0 := by
      intro i
      simp [map_sum, LinearMap.sum_apply, hd]
    have hm : v - ∑ j, h v (e j) • y j ∈ La :=
      La.sub_mem hv (La.sum_mem fun j _ => hLa _ (hIa _ hv _ (heLa j)) _ (hy j))
    have : v + ∑ j, h v (e j) • t j = (v - ∑ j, h v (e j) • y j) + ∑ j, h v (e j) • (y j + t j) := by
      simp only [smul_add, Finset.sum_add_distrib]; abel
    rw [this]
    exact Lb.add_mem ((hcap _ h0).1 hm) (Lb.sum_mem fun j _ => hLb _ (hIa _ hv _ (heLa j)) _ (hzz j))
  · have hp : ∀ i, h (n v) (e i) = h v (e i) := fun i => shear_pair h e t htE v i
    have hpO : ∀ i, h v (e i) ∈ O := fun i => by rw [← hp]; exact hIb _ hv _ (heLb i)
    have h0 : ∀ i, h (n v - ∑ j, h v (e j) • (y j + t j)) (e i) = 0 := by
      intro i
      simp [map_sum, LinearMap.sum_apply, hd, hp, htE]
    have hm : n v - ∑ j, h v (e j) • (y j + t j) ∈ Lb :=
      Lb.sub_mem hv (Lb.sum_mem fun j _ => hLb _ (hpO j) _ (hzz j))
    have : v = (n v - ∑ j, h v (e j) • (y j + t j)) + ∑ j, h v (e j) • y j := by
      rw [hn]; simp only [smul_add, Finset.sum_add_distrib]; abel
    rw [this]
    exact La.add_mem ((hcap _ h0).2 hm) (La.sum_mem fun j _ => hLa _ (hpO j) _ (hy j))

namespace Part2

/- English proof (translation)
Introduce `D _ w m om amp hm hom hamp`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[hamp d, norm_mul, hom d, one_mul, Complex.norm_real]`. Apply the tactic sequence `rcases hm d with h | h <;> simp [h]`.
-/
theorem equalityNG : EqualityNG := by
  intro D _ w m om amp hm hom hamp
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hamp d, norm_mul, hom d, one_mul, Complex.norm_real]
  rcases hm d with h | h <;> simp [h]

/- English proof (translation)
Introduce `Ov _ dens dl κ be disc tot k r hk hκ hbe hcard hdens hdl htot`. Establish `hbe0 : (0 : ℝ) < be` using `by linarith`. Establish `hpow : (be ^ (k + 2 * r + 1))⁻¹ / (be ^ (2 * r + 2))⁻¹ = (be ^ (k - 1))⁻¹`. Take `⟨k', rfl⟩` from `Nat.exists_eq_add_of_le hk`. Establish `: 1 + k' + 2 * r + 1 = k' + (2 * r + 2)` using `by ring`.

Rewrite using `[this, pow_add, Nat.add_sub_cancel_left]`. Clear the denominators using the available nonvanishing facts. Establish `hB : 0 ≤ (be ^ (k - 1))⁻¹` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun M _ => ?_` and prove the remaining obligations.

Rewrite using `[hdens M, hpow]`. Conclude with `mul_le_mul_of_nonneg_left (hdl M) (mul_nonneg hκ hB)`. Use `_ = (Fintype.card Ov : ℝ) * (κ * (be ^ (k - 1))⁻¹ * 2) := by simp`. Use `_ ≤ disc ^ (2 * r + 2) * (κ * (be ^ (k - 1))⁻¹ * 2) := mul_le_mul_of_nonneg_right hcard (by positivity)`. Use `_ = 4 * disc ^ (2 * r + 2) * (be ^ (k - 1))⁻¹ * (κ / 2) := by ring`.

Use `_ ≤ 4 * disc ^ (2 * r + 2) * (be ^ (k - 1))⁻¹ * tot := by`. Use `mul_le_mul_of_nonneg_left htot ?_` and prove the remaining obligations. Establish `: (0 : ℝ) ≤ disc ^ (2 * r + 2)` using `le_trans (Nat.cast_nonneg _) hcard`. Check the signs of the components of the expression.
-/
theorem share_first_constant : LocalDensityShareBound := by
  intro Ov _ dens dl κ be disc tot k r hk hκ hbe hcard hdens hdl htot
  have hbe0 : (0 : ℝ) < be := by linarith
  have hpow : (be ^ (k + 2 * r + 1))⁻¹ / (be ^ (2 * r + 2))⁻¹ = (be ^ (k - 1))⁻¹ := by
    obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
    have : 1 + k' + 2 * r + 1 = k' + (2 * r + 2) := by ring
    rw [this, pow_add, Nat.add_sub_cancel_left]
    field_simp
  have hB : 0 ≤ (be ^ (k - 1))⁻¹ := by positivity
  calc ∑ M, dens M ≤ ∑ _M : Ov, κ * (be ^ (k - 1))⁻¹ * 2 := by
        refine Finset.sum_le_sum fun M _ => ?_
        rw [hdens M, hpow]
        exact mul_le_mul_of_nonneg_left (hdl M) (mul_nonneg hκ hB)
    _ = (Fintype.card Ov : ℝ) * (κ * (be ^ (k - 1))⁻¹ * 2) := by simp
    _ ≤ disc ^ (2 * r + 2) * (κ * (be ^ (k - 1))⁻¹ * 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 4 * disc ^ (2 * r + 2) * (be ^ (k - 1))⁻¹ * (κ / 2) := by ring
    _ ≤ 4 * disc ^ (2 * r + 2) * (be ^ (k - 1))⁻¹ * tot := by
        refine mul_le_mul_of_nonneg_left htot ?_
        have : (0 : ℝ) ≤ disc ^ (2 * r + 2) := le_trans (Nat.cast_nonneg _) hcard
        positivity

/- English proof (translation)
Take `⟨x, hx, rfl⟩` from `ha`. Take `⟨y, hy, rfl⟩` from `hb`. Conclude with `⟨x + y, abelian₂.add_mem hx hy, (smul_add _ _ _).symm⟩`.
-/
theorem inTh_add {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {th : E} {abelian₂ : AddSubgroup V} {a b : V}
    (ha : InTh th abelian₂ a) (hb : InTh th abelian₂ b) : InTh th abelian₂ (a + b) := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact ⟨x + y, abelian₂.add_mem hx hy, (smul_add _ _ _).symm⟩

/- English proof (translation)
Take `⟨x, hx, rfl⟩` from `ha`. Conclude with `⟨c • x, hL c hc x hx, smul_comm _ _ _⟩`.
-/
theorem inTh_smul {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {O : Subring E} {th c : E}
    {abelian₂ : AddSubgroup V} {a : V} (hL : IsLat O abelian₂) (hc : c ∈ O) (ha : InTh th abelian₂ a) : InTh th abelian₂ (c • a) := by
  obtain ⟨x, hx, rfl⟩ := ha
  exact ⟨c • x, hL c hc x hx, smul_comm _ _ _⟩

/- English proof (translation)
Take `⟨x, hx, rfl⟩` from `ha`. Conclude with `⟨-x, abelian₂.neg_mem hx, (smul_neg _ _).symm⟩`.
-/
theorem inTh_neg {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {th : E} {abelian₂ : AddSubgroup V} {a : V}
    (ha : InTh th abelian₂ a) : InTh th abelian₂ (-a) := by
  obtain ⟨x, hx, rfl⟩ := ha
  exact ⟨-x, abelian₂.neg_mem hx, (smul_neg _ _).symm⟩

/- English proof (translation)
Introduce `E _ V _ _ O abelian₂ th c w₁ w₂ la₁ la₁' la₂ la₂' hL hc h1 h2`. Take `⟨a1, b1, c1⟩` from `h1`. Take `⟨a2, b2, c2⟩` from `h2`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `abelian₂.add_mem (hL c hc _ a1) a2` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_add]`. Normalize the expressions using the abelian group laws. Use `abelian₂.add_mem (hL c hc _ b1) b2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[smul_add]`. Normalize the expressions using the abelian group laws. Use `inTh_add (inTh_smul hL hc c1) c2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_sub]`.

Normalize the expressions using the abelian group laws.
-/
theorem tauLin : TauLin := by
  intro E _ V _ _ O abelian₂ th c w₁ w₂ la₁ la₁' la₂ la₂' hL hc h1 h2
  obtain ⟨a1, b1, c1⟩ := h1
  obtain ⟨a2, b2, c2⟩ := h2
  refine ⟨?_, ?_, ?_⟩
  · have := abelian₂.add_mem (hL c hc _ a1) a2
    convert this using 1
    rw [smul_add]; abel
  · have := abelian₂.add_mem (hL c hc _ b1) b2
    convert this using 1
    rw [smul_add]; abel
  · have := inTh_add (inTh_smul hL hc c1) c2
    convert this using 1
    rw [smul_sub]; abel

/- English proof (translation)
The claim follows from `abelian₂.sum_mem fun i _ => hL _ (ha i) _ (hf i)`.
-/
theorem sum_mem_lat {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {O : Subring E} {abelian₂ : AddSubgroup V}
    (hL : IsLat O abelian₂) {n : ℕ} {f : Fin n → V} {a : Fin n → E} (hf : ∀ i, f i ∈ abelian₂) (ha : ∀ i, a i ∈ O) :
    (∑ i, a i • f i) ∈ abelian₂ := abelian₂.sum_mem fun i _ => hL _ (ha i) _ (hf i)

/- English proof (translation)
Introduce `E _ V _ _ O abelian₂ θ hθ hL n f f' hli hf hf' α α' hmem`. Establish `h` using `(H E V O θ hθ n f f' hli α α').mp hmem`. Establish `hα' : ∀ i, α' i ∈ O` using `fun i => (h i).1`. Establish `hα : ∀ i, α i ∈ O` using `fun i => by`. Take `⟨x, hx, e⟩` from `(h i).2`.

Establish `: α i = θ * x - α' i` using `by rw [← e]; ring`. Rewrite using `[this]`. Conclude with `O.sub_mem (O.mul_mem hθ hx) (hα' i)`. Conclude with `⟨fun i => ⟨hα i, hα' i⟩, sum_mem_lat hL hf hα, sum_mem_lat hL hf' hα'⟩`.
-/
theorem thMParts (H : SpanCharRing) : ThMParts := by
  intro E _ V _ _ O abelian₂ θ hθ hL n f f' hli hf hf' α α' hmem
  have h := (H E V O θ hθ n f f' hli α α').mp hmem
  have hα' : ∀ i, α' i ∈ O := fun i => (h i).1
  have hα : ∀ i, α i ∈ O := fun i => by
    obtain ⟨x, hx, e⟩ := (h i).2
    have : α i = θ * x - α' i := by rw [← e]; ring
    rw [this]; exact O.sub_mem (O.mul_mem hθ hx) (hα' i)
  exact ⟨fun i => ⟨hα i, hα' i⟩, sum_mem_lat hL hf hα, sum_mem_lat hL hf' hα'⟩

/- English proof (translation)
Introduce `E _ V _ _ O abelian₂ θ hθ hL n f f' hli hf' a a' w`. Use `⟨fun hw hmem => ?_, fun hw => ⟨by simpa using hw, by simpa using hw, ⟨0, abelian₂.zero_mem, by simp⟩⟩⟩` and prove the remaining obligations. Establish `e : (∑ i, a' i • f' i) - (∑ i, a i • f i) = (∑ i, (-a i) • f i) + (∑ i, a' i • f' i)`. Simplify using `only [neg_smul, Finset.sum_neg_distrib]`. Normalize the expressions using the abelian group laws.

Rewrite `hmem` using `[e]`. Establish `h` using `(H E V O θ hθ n f f' hli (fun i => -a i) a').mp hmem`. Use `abelian₂.sub_mem hw (sum_mem_lat hL hf' (fun i => (h i).1))` as an intermediate fact. Simplify using `using this`.
-/
theorem tauKer (H : SpanCharRing) : TauKer := by
  intro E _ V _ _ O abelian₂ θ hθ hL n f f' hli hf' a a' w
  refine ⟨fun hw hmem => ?_, fun hw => ⟨by simpa using hw, by simpa using hw, ⟨0, abelian₂.zero_mem, by simp⟩⟩⟩
  have e : (∑ i, a' i • f' i) - (∑ i, a i • f i) = (∑ i, (-a i) • f i) + (∑ i, a' i • f' i) := by
    simp only [neg_smul, Finset.sum_neg_distrib]; abel
  rw [e] at hmem
  have h := (H E V O θ hθ n f f' hli (fun i => -a i) a').mp hmem
  have := abelian₂.sub_mem hw (sum_mem_lat hL hf' (fun i => (h i).1))
  simpa using this

/- English proof (translation)
Introduce `E _ _ V _ _ h O abelian₂ θ r f f' g g' a₁ a₁' a₂ a₂' a₃ a₃' w₁ w₂ c hL hI hg hg' hfg hfg' hadm hc l1 l2 l3`. Take `⟨p1, q1, t1⟩` from `l1`. Take `⟨p2, q2, t2⟩` from `l2`. Take `⟨p3, q3, t3⟩` from `l3`. Use `set γ : Fin r → E := fun i => a₃ i - c * a₁ i - a₂ i with hγ`.

Use `set γ' : Fin r → E := fun i => a₃' i - c * a₁' i - a₂' i with hγ'`. Establish `eξ : (∑ i, γ i • f i) = (∑ i, a₃ i • f i) - c • (∑ i, a₁ i • f i) - (∑ i, a₂ i • f i)`. Simplify using `only [hγ, sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]`. Establish `eξ' : (∑ i, γ' i • f' i) = (∑ i, a₃' i • f' i) - c • (∑ i, a₁' i • f' i) - (∑ i, a₂' i • f' i)`. Simplify using `only [hγ', sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]`.

Establish `hξ : (∑ i, γ i • f i) ∈ abelian₂`. Use `abelian₂.sub_mem (abelian₂.sub_mem p3 (hL c hc _ p1)) p2` as an intermediate fact. Rewrite using `[eξ]`. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_add]`.

Normalize the expressions using the abelian group laws. Establish `hξ' : (∑ i, γ' i • f' i) ∈ abelian₂`. Use `abelian₂.sub_mem (abelian₂.sub_mem q3 (hL c hc _ q1)) q2` as an intermediate fact. Rewrite using `[eξ']`. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[smul_add]`. Normalize the expressions using the abelian group laws. Establish `coef : ∀ (F G : Fin r → V) (b : Fin r → E), (∀ i j, h (F i) (G j) = if i = j then 1 else 0) → ∀ j, h (∑ i, b i • F i) (G j) = b j`. Introduce `F G b hFG j`. Simplify using `[map_sum, LinearMap.sum_apply, hFG]`.

Establish `hγ'O : ∀ i, γ' i ∈ O` using `fun i => by`. Rewrite using `[← coef f' g' γ' hfg' i]`. Conclude with `hI _ hξ' _ (hg' i)`. Establish `hdiff : InTh (θ : E) abelian₂ ((∑ i, γ' i • f' i) - (∑ i, γ i • f i))`. Use `inTh_add (inTh_add t3 (inTh_neg (inTh_smul hL hc t1))) (inTh_neg t2)` as an intermediate fact.

Rewrite using `[eξ, eξ']`. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_sub]`. Normalize the expressions using the abelian group laws. Establish `hw` using `H E V h O abelian₂ θ r f f' g γ γ' hL hI hg hfg hadm hγ'O hdiff`.

Use `choose d hdO hd using hw`. Establish `key : ((θ⁻¹ : Eˣ) : E) • (((∑ i, a₃' i • f' i) - (∑ i, a₃ i • f i)) - c • ((∑ i, a₁' i • f' i) - (∑ i, a₁ i • f i)) - ((∑ i, a₂' i • f' i) - (∑ i, a₂ i • f i))) = (∑ i, γ' i • (((θ⁻¹ : Eˣ) : E) • (f' i - f i))) + ∑ i, d i • f i`. Establish `e1 : ((∑ i, a₃' i • f' i) - (∑ i, a₃ i • f i)) - c • ((∑ i, a₁' i • f' i) - (∑ i, a₁ i • f i)) - ((∑ i, a₂' i • f' i) - (∑ i, a₂ i • f i)) = (∑ i, γ' i • f' i) - (∑ i, γ i • f i)`. Rewrite using `[eξ, eξ', smul_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e1, ← Finset.sum_sub_distrib, Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hdi : d i = ((θ⁻¹ : Eˣ) : E) * (γ' i - γ i)`. Rewrite using `[hd i, ← mul_assoc]`. Simplify using the standard rewrite rules.

Rewrite using `[hdi]`. Use `module`. Rewrite using `[key]`. Use `Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_) (Submodule.sum_mem _ fun i _ => ?_)` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ (⟨γ' i, hγ'O i⟩ : O) (Submodule.subset_span (Or.inr ⟨i, rfl⟩))`.

Conclude with `Submodule.smul_mem _ (⟨d i, hdO i⟩ : O) (Submodule.subset_span (Or.inl ⟨i, rfl⟩))`.
-/
theorem tauHom (H : TauWell) : TauHom := by
  intro E _ _ V _ _ h O abelian₂ θ r f f' g g' a₁ a₁' a₂ a₂' a₃ a₃' w₁ w₂ c hL hI hg hg' hfg hfg' hadm hc l1 l2 l3
  obtain ⟨p1, q1, t1⟩ := l1
  obtain ⟨p2, q2, t2⟩ := l2
  obtain ⟨p3, q3, t3⟩ := l3
  set γ : Fin r → E := fun i => a₃ i - c * a₁ i - a₂ i with hγ
  set γ' : Fin r → E := fun i => a₃' i - c * a₁' i - a₂' i with hγ'
  have eξ : (∑ i, γ i • f i) = (∑ i, a₃ i • f i) - c • (∑ i, a₁ i • f i) - (∑ i, a₂ i • f i) := by
    simp only [hγ, sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]
  have eξ' : (∑ i, γ' i • f' i) = (∑ i, a₃' i • f' i) - c • (∑ i, a₁' i • f' i) - (∑ i, a₂' i • f' i) := by
    simp only [hγ', sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]
  have hξ : (∑ i, γ i • f i) ∈ abelian₂ := by
    have := abelian₂.sub_mem (abelian₂.sub_mem p3 (hL c hc _ p1)) p2
    rw [eξ]; convert this using 1; rw [smul_add]; abel
  have hξ' : (∑ i, γ' i • f' i) ∈ abelian₂ := by
    have := abelian₂.sub_mem (abelian₂.sub_mem q3 (hL c hc _ q1)) q2
    rw [eξ']; convert this using 1; rw [smul_add]; abel
  have coef : ∀ (F G : Fin r → V) (b : Fin r → E), (∀ i j, h (F i) (G j) = if i = j then 1 else 0) →
      ∀ j, h (∑ i, b i • F i) (G j) = b j := by
    intro F G b hFG j
    simp [map_sum, LinearMap.sum_apply, hFG]
  have hγ'O : ∀ i, γ' i ∈ O := fun i => by
    rw [← coef f' g' γ' hfg' i]; exact hI _ hξ' _ (hg' i)
  have hdiff : InTh (θ : E) abelian₂ ((∑ i, γ' i • f' i) - (∑ i, γ i • f i)) := by
    have := inTh_add (inTh_add t3 (inTh_neg (inTh_smul hL hc t1))) (inTh_neg t2)
    rw [eξ, eξ']; convert this using 1; rw [smul_sub]; abel
  have hw := H E V h O abelian₂ θ r f f' g γ γ' hL hI hg hfg hadm hγ'O hdiff
  choose d hdO hd using hw
  have key : ((θ⁻¹ : Eˣ) : E) • (((∑ i, a₃' i • f' i) - (∑ i, a₃ i • f i))
        - c • ((∑ i, a₁' i • f' i) - (∑ i, a₁ i • f i)) - ((∑ i, a₂' i • f' i) - (∑ i, a₂ i • f i)))
      = (∑ i, γ' i • (((θ⁻¹ : Eˣ) : E) • (f' i - f i))) + ∑ i, d i • f i := by
    have e1 : ((∑ i, a₃' i • f' i) - (∑ i, a₃ i • f i))
        - c • ((∑ i, a₁' i • f' i) - (∑ i, a₁ i • f i)) - ((∑ i, a₂' i • f' i) - (∑ i, a₂ i • f i))
        = (∑ i, γ' i • f' i) - (∑ i, γ i • f i) := by
      rw [eξ, eξ', smul_sub]; abel
    rw [e1, ← Finset.sum_sub_distrib, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdi : d i = ((θ⁻¹ : Eˣ) : E) * (γ' i - γ i) := by
      rw [hd i, ← mul_assoc]; simp
    rw [hdi]
    module
  rw [key]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_) (Submodule.sum_mem _ fun i _ => ?_)
  · exact Submodule.smul_mem _ (⟨γ' i, hγ'O i⟩ : O) (Submodule.subset_span (Or.inr ⟨i, rfl⟩))
  · exact Submodule.smul_mem _ (⟨d i, hdO i⟩ : O) (Submodule.subset_span (Or.inl ⟨i, rfl⟩))

/- English proof (translation)
The claim follows from `(eichLin h x u s).map_sub v w`.
-/
theorem eich_sub {E V : Type} [CommRing E] [StarRing E] [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s : E) (v w : V) :
    eich h x u s (v - w) = eich h x u s v - eich h x u s w := (eichLin h x u s).map_sub v w

/- English proof (translation)
The claim follows from `(eichLin h x u s).map_smul c v`.
-/
theorem eich_smul {E V : Type} [CommRing E] [StarRing E] [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s c : E) (v : V) :
    eich h x u s (c • v) = c • eich h x u s v := (eichLin h x u s).map_smul c v

/- English proof (translation)
Introduce `E _ _ V _ _ h O abelian₂ th x x' u f f' s hh hth hL hI hu hsx hb hxx' hx hux hux' hs hf' hf'x' hff'`. Establish `inv` using `H2 E V h x u s hh hx hux hs`. Establish `e1 : eich h x u s (eich h x' u s f' - eich h x (-u) (star s) f) = eich h x u s (eich h x' u s f') - f`. Rewrite using `[eich_sub, (inv f).2]`. Establish `c` using `(H1 E V h O abelian₂ th x x' u s hh hth hL hI hu hsx hb hxx' hux hux' f' hf' hf'x').2.2.2`.

Establish `e2 : InTh th abelian₂ (eich h x u s (eich h x' u s f') - f)`. Use `inTh_add c hff'` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Use `⟨e1, e2, ?_⟩` and prove the remaining obligations.

Take `⟨w₀, hw₀, ew⟩` from `e2`. Use `⟨eich h x (-u) (star s) w₀, ?_, ?_⟩` and prove the remaining obligations. Use `show eich h x u s (eich h x (-u) (star s) w₀) ∈ abelian₂`. Rewrite using `[(inv w₀).2]`. Conclude with `hw₀`.

Establish `: eich h x (-u) (star s) (eich h x u s (eich h x' u s f' - eich h x (-u) (star s) f)) = eich h x (-u) (star s) (th • w₀)` using `by rw [e1, ew]`. Rewrite `this` using `[(inv _).1, eich_smul]`. Conclude with `this`.
-/
theorem moveAdm (H1 : MoveCong) (H2 : EichInv) : MoveAdm := by
  intro E _ _ V _ _ h O abelian₂ th x x' u f f' s hh hth hL hI hu hsx hb hxx' hx hux hux' hs hf' hf'x' hff'
  have inv := H2 E V h x u s hh hx hux hs
  have e1 : eich h x u s (eich h x' u s f' - eich h x (-u) (star s) f)
        = eich h x u s (eich h x' u s f') - f := by
    rw [eich_sub, (inv f).2]
  have c := (H1 E V h O abelian₂ th x x' u s hh hth hL hI hu hsx hb hxx' hux hux' f' hf' hf'x').2.2.2
  have e2 : InTh th abelian₂ (eich h x u s (eich h x' u s f') - f) := by
    have := inTh_add c hff'
    convert this using 1; abel
  refine ⟨e1, e2, ?_⟩
  obtain ⟨w₀, hw₀, ew⟩ := e2
  refine ⟨eich h x (-u) (star s) w₀, ?_, ?_⟩
  · show eich h x u s (eich h x (-u) (star s) w₀) ∈ abelian₂
    rw [(inv w₀).2]; exact hw₀
  · have : eich h x (-u) (star s) (eich h x u s (eich h x' u s f' - eich h x (-u) (star s) f))
        = eich h x (-u) (star s) (th • w₀) := by rw [e1, ew]
    rw [(inv _).1, eich_smul] at this
    exact this

/- English proof (translation)
Introduce `E _ _ V _ _ h O abelian₂ th x x' u s r e c hh hth hL hI he hx'e hx hux hux' hs hT`. Establish `perp : ∀ v, (∀ i, h v (e i) = 0) → h v x' = 0`. Introduce `v hv`. Rewrite using `[hx'e]`. Simplify using `[map_sum, hv]`.

Establish `hx'ei : ∀ i, h x' (e i) = 0`. Introduce `i`. Rewrite using `[hx'e]`. Simplify using `[map_sum, LinearMap.sum_apply, he]`. Establish `hx' : h x' x' = 0` using `perp x' hx'ei`.

Establish `M` using `H1 E V h O abelian₂ th x x' u s hh hth hL hI hx hx' hux hux' hs hT`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v₀, ⟨hv₀, hv₀e⟩, rfl⟩`. Establish `h1 : eich h x' u s v₀ ∈ {v | v ∈ moved h x u s abelian₂ ∧ h v x' = 0}`.

Rewrite using `[← M]`. Conclude with `⟨v₀, ⟨hv₀, perp v₀ hv₀e⟩, rfl⟩`. Use `⟨h1.1, fun i => ?_⟩` and prove the remaining obligations. Simplify using `[eich, perp v₀ hv₀e, hv₀e i, hx'ei i]`. Introduce and unpack `⟨hv, hve⟩`.

Establish `h1 : v ∈ eich h x' u s '' {v | v ∈ abelian₂ ∧ h v x' = 0}`. Rewrite using `[M]`. Conclude with `⟨hv, perp v hve⟩`. Take `⟨v₀, ⟨hv₀, hv₀x⟩, rfl⟩` from `h1`. Use `⟨v₀, ⟨hv₀, fun i => ?_⟩, rfl⟩` and prove the remaining obligations.

Use `hve i` as an intermediate fact. Simplify `this` using `[eich, hv₀x, hx'ei i]`.
-/
theorem movePerpX (H1 : MovePerp) : MovePerpX := by
  intro E _ _ V _ _ h O abelian₂ th x x' u s r e c hh hth hL hI he hx'e hx hux hux' hs hT
  have perp : ∀ v, (∀ i, h v (e i) = 0) → h v x' = 0 := by
    intro v hv; rw [hx'e]; simp [map_sum, hv]
  have hx'ei : ∀ i, h x' (e i) = 0 := by
    intro i; rw [hx'e]; simp [map_sum, LinearMap.sum_apply, he]
  have hx' : h x' x' = 0 := perp x' hx'ei
  have M := H1 E V h O abelian₂ th x x' u s hh hth hL hI hx hx' hux hux' hs hT
  ext v
  constructor
  · rintro ⟨v₀, ⟨hv₀, hv₀e⟩, rfl⟩
    have h1 : eich h x' u s v₀ ∈ {v | v ∈ moved h x u s abelian₂ ∧ h v x' = 0} := by
      rw [← M]; exact ⟨v₀, ⟨hv₀, perp v₀ hv₀e⟩, rfl⟩
    refine ⟨h1.1, fun i => ?_⟩
    simp [eich, perp v₀ hv₀e, hv₀e i, hx'ei i]
  · rintro ⟨hv, hve⟩
    have h1 : v ∈ eich h x' u s '' {v | v ∈ abelian₂ ∧ h v x' = 0} := by
      rw [M]; exact ⟨hv, perp v hve⟩
    obtain ⟨v₀, ⟨hv₀, hv₀x⟩, rfl⟩ := h1
    refine ⟨v₀, ⟨hv₀, fun i => ?_⟩, rfl⟩
    have := hve i
    simpa [eich, hv₀x, hx'ei i] using this

/- English proof (translation)
Introduce `o O S _ _ _ _ _ _ _ _ _ ϖ pr τ ψ q N i n Gm φ hU hϖ hq hq2 hsur hker _ hiN hτ hψ hG hφ1 hφ`. Establish `A` using `H2 o O S ϖ pr τ ψ q N i hU hϖ hq hq2 hsur hker hiN hτ hψ`. Establish `B` using `H1 S n Gm ψ φ hG hφ1 hφ`. Rewrite `B` using `[A.2]`. Establish `hS : (Fintype.card S : ℝ) = (q : ℝ) ^ (2 * N)`.

Rewrite using `[← Nat.card_eq_fintype_card, A.1]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast (by omega : 0 < q)`. Rewrite `B`, the goal using `[hS]`.

Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le hiN`. Rewrite `B` using `[Nat.add_sub_cancel_left]`. Establish `e : ((q : ℝ) ^ (i * n))⁻¹ * ((q : ℝ) ^ (2 * (i + m))) ^ n = (q : ℝ) ^ ((i + 2 * m) * n)`. Rewrite using `[← pow_mul, inv_mul_eq_div, div_eq_iff (by positivity), ← pow_add]; congr 1; ring`. Rewrite using `[e]`.

Use `(sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (B.trans (le_of_eq ?_))` and prove the remaining obligations. Use `push_cast`. Rewrite using `[← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermGaussCond (H1 : HermGaussRing) (H2 : AnnihSize) : HermGaussCond := by
  intro o O S _ _ _ _ _ _ _ _ _ ϖ pr τ ψ q N i n Gm φ hU hϖ hq hq2 hsur hker _ hiN hτ hψ hG hφ1 hφ
  have A := H2 o O S ϖ pr τ ψ q N i hU hϖ hq hq2 hsur hker hiN hτ hψ
  have B := H1 S n Gm ψ φ hG hφ1 hφ
  rw [A.2] at B
  have hS : (Fintype.card S : ℝ) = (q : ℝ) ^ (2 * N) := by
    rw [← Nat.card_eq_fintype_card, A.1]; push_cast; rfl
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [hS] at B ⊢
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hiN
  rw [Nat.add_sub_cancel_left] at B
  have e : ((q : ℝ) ^ (i * n))⁻¹ * ((q : ℝ) ^ (2 * (i + m))) ^ n = (q : ℝ) ^ ((i + 2 * m) * n) := by
    rw [← pow_mul, inv_mul_eq_div, div_eq_iff (by positivity), ← pow_add]; congr 1; ring
  rw [e]
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (B.trans (le_of_eq ?_))
  push_cast
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring

/- English proof (translation)
Introduce `o O' Lam' _ _ _ _ _ _ _ _ _ _ h' E _ _ V _ _ h O abelian₂ io j hU hSD hM hunit hspan Z y hy`. Set `S' : Submodule O' Lam'` to `{ carrier := {v | j v ∈ Z} add_mem' := fun {a b} ha hb => by show j (a + b) ∈ Z`. Rewrite using `[map_add]`. Conclude with `Z.add_mem ha hb`. Use the proof step `zero_mem' := by show j 0 ∈ Z`.

Rewrite using `[map_zero]`. Conclude with `Z.zero_mem`. Use the proof step `smul_mem' := fun a v hv => by show j (a • v) ∈ Z`. Rewrite using `[hM.j_smul]`. Conclude with `Z.smul_mem _ hv }`.

Establish `hsat : Satur o S'`. Introduce `c v hc hmem`. Establish `h1 : io (algebraMap o O' c) • j v ∈ Z` using `by rw [← hM.j_smul]; exact hmem`. Take `⟨u, hu⟩` from `hunit c hc`. Establish `h2 : j v = ((u⁻¹ : Eˣ) : E) • (io (algebraMap o O' c) • j v)`.

Rewrite using `[← hu, smul_smul]`. Simplify using the standard rewrite rules. Use `show j v ∈ Z`. Rewrite using `[h2]`. Conclude with `Z.smul_mem _ h1`.

Establish `hex : ∀ v : S', ∃ a, io a = h (j v) y` using `fun v => (hM.io_range _).mp (hy (j v) ((hM.j_range _).mpr ⟨v, rfl⟩) v.2)`. Use `choose F hF using hex`. Set `φ : S' →ₗ[O'] O'` to `{ toFun := F map_add' := fun a b => hM.io_inj (by`. Rewrite using `[map_add, hF, hF, hF]`. Use the proof step `simp)`.

Use the proof step `map_smul' := fun c a => hM.io_inj (by`. Rewrite using `[hF, RingHom.id_apply, smul_eq_mul, map_mul, hF]`. Simplify using `[hM.j_smul]) }`. Take `⟨w, hw⟩` from `H o O' Lam' h' hU hSD S' hsat φ`. Use `⟨j w, (hM.j_range _).mpr ⟨w, rfl⟩, fun z hz => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc, hcz⟩` from `hspan z`. Take `⟨v', hv'⟩` from `(hM.j_range _).mp hcz`. Establish `hv'S : v' ∈ S'` using `by show j v' ∈ Z`. Rewrite using `[hv']`. Conclude with `Z.smul_mem _ hz`.

Establish `h1 : h (j v') y = h (j v') (j w)`. Use `hw ⟨v', hv'S⟩` as an intermediate fact. Establish `h2 : io (F ⟨v', hv'S⟩) = io (h' v' w)` using `congrArg io this`. Rewrite `h2` using `[hF, ← hM.form]`. Conclude with `h2`.

Rewrite `h1` using `[hv']`. Establish `h3 : io (algebraMap o O' c) * h z (y - j w) = 0`. Establish `: h (io (algebraMap o O' c) • z) (y - j w) = 0` using `by rw [map_sub, h1, sub_self]`. Simplify using `using this`. Conclude with `(hunit c hc).mul_right_eq_zero.mp h3`.
-/
theorem dualCapV (H : DualCap) : DualCapV := by
  intro o O' Lam' _ _ _ _ _ _ _ _ _ _ h' E _ _ V _ _ h O abelian₂ io j hU hSD hM hunit hspan Z y hy
  let S' : Submodule O' Lam' :=
    { carrier := {v | j v ∈ Z}
      add_mem' := fun {a b} ha hb => by
        show j (a + b) ∈ Z
        rw [map_add]; exact Z.add_mem ha hb
      zero_mem' := by
        show j 0 ∈ Z
        rw [map_zero]; exact Z.zero_mem
      smul_mem' := fun a v hv => by
        show j (a • v) ∈ Z
        rw [hM.j_smul]; exact Z.smul_mem _ hv }
  have hsat : Satur o S' := by
    intro c v hc hmem
    have h1 : io (algebraMap o O' c) • j v ∈ Z := by rw [← hM.j_smul]; exact hmem
    obtain ⟨u, hu⟩ := hunit c hc
    have h2 : j v = ((u⁻¹ : Eˣ) : E) • (io (algebraMap o O' c) • j v) := by
      rw [← hu, smul_smul]; simp
    show j v ∈ Z
    rw [h2]; exact Z.smul_mem _ h1
  have hex : ∀ v : S', ∃ a, io a = h (j v) y := fun v =>
    (hM.io_range _).mp (hy (j v) ((hM.j_range _).mpr ⟨v, rfl⟩) v.2)
  choose F hF using hex
  let φ : S' →ₗ[O'] O' :=
    { toFun := F
      map_add' := fun a b => hM.io_inj (by
        rw [map_add, hF, hF, hF]; simp)
      map_smul' := fun c a => hM.io_inj (by
        rw [hF, RingHom.id_apply, smul_eq_mul, map_mul, hF]; simp [hM.j_smul]) }
  obtain ⟨w, hw⟩ := H o O' Lam' h' hU hSD S' hsat φ
  refine ⟨j w, (hM.j_range _).mpr ⟨w, rfl⟩, fun z hz => ?_⟩
  obtain ⟨c, hc, hcz⟩ := hspan z
  obtain ⟨v', hv'⟩ := (hM.j_range _).mp hcz
  have hv'S : v' ∈ S' := by
    show j v' ∈ Z
    rw [hv']; exact Z.smul_mem _ hz
  have h1 : h (j v') y = h (j v') (j w) := by
    have := hw ⟨v', hv'S⟩
    have h2 : io (F ⟨v', hv'S⟩) = io (h' v' w) := congrArg io this
    rw [hF, ← hM.form] at h2
    exact h2
  rw [hv'] at h1
  have h3 : io (algebraMap o O' c) * h z (y - j w) = 0 := by
    have : h (io (algebraMap o O' c) • z) (y - j w) = 0 := by rw [map_sub, h1, sub_self]
    simpa using this
  exact (hunit c hc).mul_right_eq_zero.mp h3

/- English proof (translation)
Introduce `S _ _ P n`. Establish `e : {u : Fin n → S // ∀ k, u k ∈ P} ≃ (Fin n → P)` using `{ toFun := fun u k => ⟨u.1 k, u.2 k⟩ invFun := fun u => ⟨fun k => (u k).1, fun k => (u k).2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Rewrite using `[Nat.card_congr e, Nat.card_fun, Nat.card_fin, ← mul_pow]`. Use `congr 1`. Use `Submodule.card_eq_card_quotient_mul_card P` as an intermediate fact.

Rewrite using `[this, mul_comm]`.
-/
theorem leakProb : LeakProb := by
  intro S _ _ P n
  have e : {u : Fin n → S // ∀ k, u k ∈ P} ≃ (Fin n → P) :=
    { toFun := fun u k => ⟨u.1 k, u.2 k⟩
      invFun := fun u => ⟨fun k => (u k).1, fun k => (u k).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_fin, ← mul_pow]
  congr 1
  have := Submodule.card_eq_card_quotient_mul_card P
  rw [this, mul_comm]

/- English proof (translation)
Introduce `c`. Use `⟨4 * c, ?_⟩` and prove the remaining obligations. Introduce `k e H nn D Ty _ _ w amp μ be I hH hnn hw hcard hbe hI hIbe hμ hμI hsum hamp`. Use `set A : ℝ := H ^ (c * e) with hA`. Establish `hA0 : 0 ≤ A` using `by positivity`.

Establish `step : ∀ t, ∑ d, w d * ‖amp t d‖ ^ 2 ≤ A * A * nn`. Introduce `t`. Establish `hb : 0 < be t ^ (k - 1)` using `by have := hbe t; positivity`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun d _ => ?_` and prove the remaining obligations.

Establish `h1 : ‖amp t d‖ ^ 2 ≤ (A * I t ^ (k - 1)) * μ t d`. Combine the equalities or inequalities in the displayed calculation. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (hamp t d) 2`. Use `_ = μ t d * μ t d := by ring`. Use `_ ≤ (A * I t ^ (k - 1)) * μ t d := mul_le_mul_of_nonneg_right (hμI t d) (hμ t d)`.

Combine the equalities or inequalities in the displayed calculation. Use `_ = (A * I t ^ (k - 1)) * ∑ d, w d * μ t d := by rw [Finset.mul_sum]`. Use `_ ≤ (A * I t ^ (k - 1)) * (A * (be t ^ (k - 1))⁻¹ * nn) := mul_le_mul_of_nonneg_left (hsum t) (mul_nonneg hA0 (pow_nonneg (hI t) _))`. Use `_ = A * A * nn * (I t ^ (k - 1) * (be t ^ (k - 1))⁻¹) := by ring`. Use `_ ≤ A * A * nn * 1 := by`.

Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations. Rewrite using `[← div_eq_mul_inv, div_le_one hb]`. Conclude with `pow_le_pow_left₀ (hI t) (hIbe t) _`. Use `_ = A * A * nn := by ring`. Combine the equalities or inequalities in the displayed calculation.

Use `mul_le_mul_of_nonneg_right ?_ (by positivity)` and prove the remaining obligations. Conclude with `mul_le_mul hcard hcard (Nat.cast_nonneg _) hA0`. Use `_ = H ^ (4 * c * e) * nn := by`. Rewrite using `[hA, ← mul_assoc, ← pow_add, ← pow_add]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem assemblyNG2 (H1 : TypeCS) : AssemblyNG2 := by
  intro c
  refine ⟨4 * c, ?_⟩
  intro k e H nn D Ty _ _ w amp μ be I hH hnn hw hcard hbe hI hIbe hμ hμI hsum hamp
  set A : ℝ := H ^ (c * e) with hA
  have hA0 : 0 ≤ A := by positivity
  have step : ∀ t, ∑ d, w d * ‖amp t d‖ ^ 2 ≤ A * A * nn := by
    intro t
    have hb : 0 < be t ^ (k - 1) := by have := hbe t; positivity
    calc ∑ d, w d * ‖amp t d‖ ^ 2 ≤ ∑ d, (A * I t ^ (k - 1)) * (w d * μ t d) := by
          refine Finset.sum_le_sum fun d _ => ?_
          have h1 : ‖amp t d‖ ^ 2 ≤ (A * I t ^ (k - 1)) * μ t d := by
            calc ‖amp t d‖ ^ 2 ≤ μ t d ^ 2 := by
                  exact pow_le_pow_left₀ (norm_nonneg _) (hamp t d) 2
              _ = μ t d * μ t d := by ring
              _ ≤ (A * I t ^ (k - 1)) * μ t d := mul_le_mul_of_nonneg_right (hμI t d) (hμ t d)
          calc w d * ‖amp t d‖ ^ 2 ≤ w d * ((A * I t ^ (k - 1)) * μ t d) :=
                mul_le_mul_of_nonneg_left h1 (hw d)
            _ = _ := by ring
      _ = (A * I t ^ (k - 1)) * ∑ d, w d * μ t d := by rw [Finset.mul_sum]
      _ ≤ (A * I t ^ (k - 1)) * (A * (be t ^ (k - 1))⁻¹ * nn) :=
          mul_le_mul_of_nonneg_left (hsum t) (mul_nonneg hA0 (pow_nonneg (hI t) _))
      _ = A * A * nn * (I t ^ (k - 1) * (be t ^ (k - 1))⁻¹) := by ring
      _ ≤ A * A * nn * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← div_eq_mul_inv, div_le_one hb]
          exact pow_le_pow_left₀ (hI t) (hIbe t) _
      _ = A * A * nn := by ring
  calc ∑ d, w d * ‖∑ t, amp t d‖ ^ 2 ≤ (Fintype.card Ty : ℝ) * ∑ t, ∑ d, w d * ‖amp t d‖ ^ 2 :=
        H1 D Ty w amp hw
    _ ≤ (Fintype.card Ty : ℝ) * ∑ _t : Ty, A * A * nn :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => step t) (Nat.cast_nonneg _)
    _ = (Fintype.card Ty : ℝ) * (Fintype.card Ty : ℝ) * (A * A * nn) := by simp; ring
    _ ≤ A * A * (A * A * nn) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul hcard hcard (Nat.cast_nonneg _) hA0
    _ = H ^ (4 * c * e) * nn := by
        rw [hA, ← mul_assoc, ← pow_add, ← pow_add]; congr 2; ring

/- English proof (translation)
Introduce `C₁ C₂`. Use `⟨|C₁| * (1 + |C₁|) + 2 * |C₂|, ?_⟩` and prove the remaining obligations. Introduce `B U Pl X Mv _ _ _ _ _ _ _ _ vol Z UP jj χ bb uu tgt μ ω ω₀ q a ρ hq hρ hPl hjj hU hvol hVB hμ hW hZ hχZ hχ1 hUP hleak htgt hω`. Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast (by omega : 0 < q)`. Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast (by omega : 1 ≤ q)`.

Use `set δ : ℝ := (q : ℝ) ^ (1 - (ρ : ℤ)) with hδ`. Establish `hδ0 : 0 < δ` using `zpow_pos hq0 _`. Establish `hδ1 : δ ≤ 1` using `zpow_le_one_of_nonpos₀ hq1 (by omega)`. Establish `hU0 : (0 : ℝ) < Fintype.card U` using `by exact_mod_cast hU`. Use `set N : ℝ := (Fintype.card U : ℝ) / (q : ℝ) ^ a with hN`.

Establish `hN0 : 0 < N` using `by positivity`. Use `set VB : ℝ := ∑ b, vol b with hVBdef`. Establish `fib : ∀ g : B → U → ℂ, ∑ m, (μ m : ℂ) * g (bb m) (uu m) = ∑ b, ∑ u ∈ Z, ((vol b / (VB * N) : ℝ) : ℂ) * g b u`. Introduce `g`. Rewrite using `[← Finset.sum_fiberwise (s := univ) (g := fun m => (bb m, uu m)), Fintype.sum_prod_type]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_filter_add_sum_filter_not univ (fun u => u ∈ Z)]`. Establish `hz : ∑ u ∈ univ.filter (fun u => ¬ u ∈ Z), ∑ m ∈ univ.filter (fun m => (bb m, uu m) = (b, u)), (μ m : ℂ) * g (bb m) (uu m) = 0`. Use `Finset.sum_eq_zero fun u hu => ?_` and prove the remaining obligations. Establish `hu' : u ∉ Z` using `(Finset.mem_filter.mp hu).2`.

Establish `h0` using `hW b u`. Rewrite `h0` using `[if_neg hu']`. Use `Finset.sum_eq_zero fun m hm => ?_` and prove the remaining obligations. Establish `hm' : bb m = b ∧ uu m = u` using `by simpa using (Finset.mem_filter.mp hm).2`. Establish `: μ m = 0` using `(Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hμ i)).mp h0 m (by simp [hm'.1, hm'.2])`.

Simplify using `[this]`. Rewrite using `[hz, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]`. Use `Finset.sum_congr rfl fun u hu => ?_` and prove the remaining obligations. Establish `h0` using `hW b u`. Rewrite `h0` using `[if_pos hu]`.

Rewrite using `[← h0]`. Use `push_cast`. Rewrite using `[Finset.sum_mul]`. Establish `hf : univ.filter (fun m => (bb m, uu m) = (b, u)) = univ.filter (fun m => bb m = b ∧ uu m = u)`. Use extensionality with `m`.

Simplify using the standard rewrite rules. Rewrite using `[hf]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hm'` using `(Finset.mem_filter.mp hm).2`. Rewrite using `[hm'.1, hm'.2]`.

Establish `fibR : ∀ g : B → U → ℝ, ∑ m, μ m * g (bb m) (uu m) = ∑ b, ∑ u ∈ Z, vol b / (VB * N) * g b u`. Introduce `g`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Use `push_cast`. Use `fib (fun b u => (g b u : ℂ))` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Establish `volsum : ∀ t : ℝ, ∑ b, vol b / (VB * N) * t = t / N`. Introduce `t`. Rewrite using `[← Finset.sum_mul, ← Finset.sum_div, ← hVBdef]`.

Clear the denominators using the available nonvanishing facts. Establish `hT : ∑ m, μ m = (Z.card : ℝ) / N`. Use `fibR (fun _ _ => 1)` as an intermediate fact. Simplify using `only [mul_one, Finset.sum_const, nsmul_eq_mul] at this`. Rewrite using `[this, ← volsum (Z.card : ℝ)]`.

Conclude with `Finset.sum_congr rfl fun b _ => by ring`. Establish `hTerr : |(Z.card : ℝ) / N - 1| ≤ |C₁| * δ`. Establish `: (Z.card : ℝ) / N - 1 = ((Z.card : ℝ) - N) / N` using `by field_simp`. Rewrite using `[this, abs_div, abs_of_pos hN0, div_le_iff₀ hN0]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hZN : (Z.card : ℝ) / N ≤ 1 + |C₁|`. Use `(abs_le.mp hTerr).2` as an intermediate fact. Establish `h2 : |C₁| * δ ≤ |C₁|` using `mul_le_of_le_one_right (abs_nonneg _) hδ1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hP : ∀ P, ∑ m, μ m * (if uu m ∈ UP P then 1 else 0) ≤ |C₂| * δ`.

Introduce `P`. Use `fibR (fun _ u => if u ∈ UP P then 1 else 0)` as an intermediate fact. Rewrite using `[this]`. Establish `h1 : ∀ b, ∑ u ∈ Z, vol b / (VB * N) * (if u ∈ UP P then (1 : ℝ) else 0) = vol b / (VB * N) * ((Z ∩ UP P).card : ℝ)`. Introduce `b`.

Rewrite using `[← Finset.mul_sum, Finset.sum_ite_mem]`. Simplify using the standard rewrite rules. Simplify using `only [h1]`. Rewrite using `[volsum, div_le_iff₀ hN0]`. Establish `hpw : (q : ℝ) ^ jj P * ((q : ℝ) ^ (jj P * ρ))⁻¹ ≤ δ`.

Take `⟨j', hj'⟩` from `Nat.exists_eq_add_of_le (hjj P)`. Establish `e : (q : ℝ) ^ jj P * ((q : ℝ) ^ (jj P * ρ))⁻¹ = δ ^ jj P`. Rewrite using `[hδ, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hq0.ne', ← zpow_natCast, ← zpow_mul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hj', pow_add, pow_one]`. Conclude with `mul_le_of_le_one_right hδ0.le (pow_le_one₀ hδ0.le hδ1)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hUP P, hN]`.

Clear the denominators using the available nonvanishing facts. Use `_ ≤ |C₂| * ((q : ℝ) ^ jj P * ((q : ℝ) ^ (jj P * ρ))⁻¹) * N := by gcongr; exact le_abs_self _`. Use `_ ≤ |C₂| * δ * N := by gcongr`. Establish `hL : ∑ m ∈ univ.filter (fun m => tgt m = none), μ m ≤ 2 * |C₂| * δ`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_le_sum fun m hm => ?_` and prove the remaining obligations. Take `⟨P, hPm⟩` from `htgt m (Finset.mem_filter.mp hm).2`. Combine the equalities or inequalities in the displayed calculation. Apply the tactic sequence `_ ≤ ∑ m, ∑ P, μ m * (if uu m ∈ UP P then 1 else 0) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun m _ _ => Finset.sum_nonneg fun P' _ => mul_nonneg (hμ m) (by split_ifs <;> norm_num)`. Use `_ = ∑ P, ∑ m, μ m * (if uu m ∈ UP P then 1 else 0) := Finset.sum_comm`.

Use `_ ≤ ∑ _P : Pl, |C₂| * δ := Finset.sum_le_sum fun P _ => hP P`. Use `_ = (Fintype.card Pl : ℝ) * (|C₂| * δ) := by simp`. Use `_ ≤ 2 * (|C₂| * δ) := by`. Use `mul_le_mul_of_nonneg_right (by exact_mod_cast hPl) (by positivity)` and prove the remaining obligations. Use `_ = 2 * |C₂| * δ := by ring`.

Establish `hL0 : 0 ≤ ∑ m ∈ univ.filter (fun m => tgt m = none), μ m` using `Finset.sum_nonneg fun m _ => hμ m`. Establish `split : ∀ F : Mv → ℂ, ∑ x, ∑ m ∈ univ.filter (fun m => tgt m = some x), F m = ∑ m, F m - ∑ m ∈ univ.filter (fun m => tgt m = none), F m`. Introduce `F`. Rewrite using `[← Finset.sum_fiberwise (s := univ) (g := tgt) (f := F), Fintype.sum_option]`. Expand and normalize the polynomial expressions, which then agree.

Establish `splitR : ∑ x, ∑ m ∈ univ.filter (fun m => tgt m = some x), μ m = ∑ m, μ m - ∑ m ∈ univ.filter (fun m => tgt m = none), μ m`. Rewrite using `[← Finset.sum_fiberwise (s := univ) (g := tgt) (f := μ), Fintype.sum_option]`. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Rewrite using `[splitR, hT]`.

Establish `h1` using `abs_le.mp hTerr`. Establish `h3 : |C₁| * δ ≤ |C₁| * (1 + |C₁|) * δ`. Establish `: |C₁| ≤ |C₁| * (1 + |C₁|)` using `le_mul_of_one_le_right (abs_nonneg _) (by linarith [abs_nonneg C₁])`. Use `gcongr`. Rewrite using `[abs_le]`.

Apply the tactic sequence `constructor <;> nlinarith [h1.1, h1.2]`. Establish `e1 : ∑ x, ((∑ m ∈ univ.filter (fun m => tgt m = some x), μ m : ℝ) : ℂ) * ω x = ω₀ * ∑ x, ∑ m ∈ univ.filter (fun m => tgt m = some x), (μ m : ℂ) * χ (bb m) (uu m)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[hω m x (Finset.mem_filter.mp hm).2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, split, norm_mul, mul_comm]`.

Use `mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)` and prove the remaining obligations. Establish `n1 : ‖∑ m, (μ m : ℂ) * χ (bb m) (uu m)‖ ≤ |C₁| * (1 + |C₁|) * δ`. Rewrite using `[fib]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.mul_sum, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by have := hvol b; positivity)]`. Use `mul_le_mul_of_nonneg_left ?_ (by have := hvol b; positivity)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `_ = |C₁| * δ * ((Z.card : ℝ) / N) := by rw [volsum]; ring`. Use `_ ≤ |C₁| * δ * (1 + |C₁|) := by gcongr`.

Use `_ = _ := by ring`. Establish `n2 : ‖∑ m ∈ univ.filter (fun m => tgt m = none), (μ m : ℂ) * χ (bb m) (uu m)‖ ≤ 2 * |C₂| * δ`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, hχ1, mul_one, Complex.norm_real, Real.norm_of_nonneg (hμ m)]`.

Use `_ ≤ _ := hL`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rowSums : RowSums := by
  intro C₁ C₂
  refine ⟨|C₁| * (1 + |C₁|) + 2 * |C₂|, ?_⟩
  intro B U Pl X Mv _ _ _ _ _ _ _ _ vol Z UP jj χ bb uu tgt μ ω ω₀ q a ρ hq hρ hPl hjj hU hvol hVB hμ hW hZ hχZ
    hχ1 hUP hleak htgt hω
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  set δ : ℝ := (q : ℝ) ^ (1 - (ρ : ℤ)) with hδ
  have hδ0 : 0 < δ := zpow_pos hq0 _
  have hδ1 : δ ≤ 1 := zpow_le_one_of_nonpos₀ hq1 (by omega)
  have hU0 : (0 : ℝ) < Fintype.card U := by exact_mod_cast hU
  set N : ℝ := (Fintype.card U : ℝ) / (q : ℝ) ^ a with hN
  have hN0 : 0 < N := by positivity
  set VB : ℝ := ∑ b, vol b with hVBdef

  have fib : ∀ g : B → U → ℂ, ∑ m, (μ m : ℂ) * g (bb m) (uu m)
      = ∑ b, ∑ u ∈ Z, ((vol b / (VB * N) : ℝ) : ℂ) * g b u := by
    intro g
    rw [← Finset.sum_fiberwise (s := univ) (g := fun m => (bb m, uu m)), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun u => u ∈ Z)]
    have hz : ∑ u ∈ univ.filter (fun u => ¬ u ∈ Z),
        ∑ m ∈ univ.filter (fun m => (bb m, uu m) = (b, u)), (μ m : ℂ) * g (bb m) (uu m) = 0 := by
      refine Finset.sum_eq_zero fun u hu => ?_
      have hu' : u ∉ Z := (Finset.mem_filter.mp hu).2
      have h0 := hW b u
      rw [if_neg hu'] at h0
      refine Finset.sum_eq_zero fun m hm => ?_
      have hm' : bb m = b ∧ uu m = u := by simpa using (Finset.mem_filter.mp hm).2
      have : μ m = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hμ i)).mp h0 m (by simp [hm'.1, hm'.2])
      simp [this]
    rw [hz, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl fun u hu => ?_
    have h0 := hW b u
    rw [if_pos hu] at h0
    rw [← h0]
    push_cast
    rw [Finset.sum_mul]
    have hf : univ.filter (fun m => (bb m, uu m) = (b, u)) = univ.filter (fun m => bb m = b ∧ uu m = u) := by
      ext m; simp
    rw [hf]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := (Finset.mem_filter.mp hm).2
    rw [hm'.1, hm'.2]
  have fibR : ∀ g : B → U → ℝ, ∑ m, μ m * g (bb m) (uu m) = ∑ b, ∑ u ∈ Z, vol b / (VB * N) * g b u := by
    intro g
    apply Complex.ofReal_injective
    push_cast
    have := fib (fun b u => (g b u : ℂ))
    push_cast at this
    exact this
  have volsum : ∀ t : ℝ, ∑ b, vol b / (VB * N) * t = t / N := by
    intro t
    rw [← Finset.sum_mul, ← Finset.sum_div, ← hVBdef]
    field_simp

  have hT : ∑ m, μ m = (Z.card : ℝ) / N := by
    have := fibR (fun _ _ => 1)
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at this
    rw [this, ← volsum (Z.card : ℝ)]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hTerr : |(Z.card : ℝ) / N - 1| ≤ |C₁| * δ := by
    have : (Z.card : ℝ) / N - 1 = ((Z.card : ℝ) - N) / N := by field_simp
    rw [this, abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
    calc |(Z.card : ℝ) - N| ≤ C₁ * δ * N := hZ
      _ ≤ |C₁| * δ * N := by gcongr; exact le_abs_self _
  have hZN : (Z.card : ℝ) / N ≤ 1 + |C₁| := by
    have := (abs_le.mp hTerr).2
    have h2 : |C₁| * δ ≤ |C₁| := mul_le_of_le_one_right (abs_nonneg _) hδ1
    linarith

  have hP : ∀ P, ∑ m, μ m * (if uu m ∈ UP P then 1 else 0) ≤ |C₂| * δ := by
    intro P
    have := fibR (fun _ u => if u ∈ UP P then 1 else 0)
    rw [this]
    have h1 : ∀ b, ∑ u ∈ Z, vol b / (VB * N) * (if u ∈ UP P then (1 : ℝ) else 0)
        = vol b / (VB * N) * ((Z ∩ UP P).card : ℝ) := by
      intro b
      rw [← Finset.mul_sum, Finset.sum_ite_mem]; simp
    simp only [h1]
    rw [volsum, div_le_iff₀ hN0]
    have hpw : (q : ℝ) ^ jj P * ((q : ℝ) ^ (jj P * ρ))⁻¹ ≤ δ := by
      obtain ⟨j', hj'⟩ := Nat.exists_eq_add_of_le (hjj P)
      have e : (q : ℝ) ^ jj P * ((q : ℝ) ^ (jj P * ρ))⁻¹ = δ ^ jj P := by
        rw [hδ, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hq0.ne', ← zpow_natCast, ← zpow_mul]
        congr 1; push_cast; ring
      rw [e, hj', pow_add, pow_one]
      exact mul_le_of_le_one_right hδ0.le (pow_le_one₀ hδ0.le hδ1)
    calc ((Z ∩ UP P).card : ℝ) ≤ C₂ * (q : ℝ) ^ jj P * (((UP P).card : ℝ) / (q : ℝ) ^ a) := hleak P
      _ = C₂ * ((q : ℝ) ^ jj P * ((q : ℝ) ^ (jj P * ρ))⁻¹) * N := by
          rw [hUP P, hN]; field_simp
      _ ≤ |C₂| * ((q : ℝ) ^ jj P * ((q : ℝ) ^ (jj P * ρ))⁻¹) * N := by
          gcongr; exact le_abs_self _
      _ ≤ |C₂| * δ * N := by gcongr
  have hL : ∑ m ∈ univ.filter (fun m => tgt m = none), μ m ≤ 2 * |C₂| * δ := by
    calc ∑ m ∈ univ.filter (fun m => tgt m = none), μ m
        ≤ ∑ m ∈ univ.filter (fun m => tgt m = none), ∑ P, μ m * (if uu m ∈ UP P then 1 else 0) := by
          refine Finset.sum_le_sum fun m hm => ?_
          obtain ⟨P, hPm⟩ := htgt m (Finset.mem_filter.mp hm).2
          calc μ m = μ m * (if uu m ∈ UP P then 1 else 0) := by rw [if_pos hPm, mul_one]
            _ ≤ _ := Finset.single_le_sum (f := fun P => μ m * (if uu m ∈ UP P then (1 : ℝ) else 0))
                  (fun P' _ => mul_nonneg (hμ m) (by split_ifs <;> norm_num)) (Finset.mem_univ P)
      _ ≤ ∑ m, ∑ P, μ m * (if uu m ∈ UP P then 1 else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun m _ _ =>
            Finset.sum_nonneg fun P' _ => mul_nonneg (hμ m) (by split_ifs <;> norm_num)
      _ = ∑ P, ∑ m, μ m * (if uu m ∈ UP P then 1 else 0) := Finset.sum_comm
      _ ≤ ∑ _P : Pl, |C₂| * δ := Finset.sum_le_sum fun P _ => hP P
      _ = (Fintype.card Pl : ℝ) * (|C₂| * δ) := by simp
      _ ≤ 2 * (|C₂| * δ) := by
          refine mul_le_mul_of_nonneg_right (by exact_mod_cast hPl) (by positivity)
      _ = 2 * |C₂| * δ := by ring
  have hL0 : 0 ≤ ∑ m ∈ univ.filter (fun m => tgt m = none), μ m := Finset.sum_nonneg fun m _ => hμ m

  have split : ∀ F : Mv → ℂ, ∑ x, ∑ m ∈ univ.filter (fun m => tgt m = some x), F m
      = ∑ m, F m - ∑ m ∈ univ.filter (fun m => tgt m = none), F m := by
    intro F
    rw [← Finset.sum_fiberwise (s := univ) (g := tgt) (f := F), Fintype.sum_option]; ring
  have splitR : ∑ x, ∑ m ∈ univ.filter (fun m => tgt m = some x), μ m
      = ∑ m, μ m - ∑ m ∈ univ.filter (fun m => tgt m = none), μ m := by
    rw [← Finset.sum_fiberwise (s := univ) (g := tgt) (f := μ), Fintype.sum_option]; ring
  constructor
  · rw [splitR, hT]
    have h1 := abs_le.mp hTerr
    have h3 : |C₁| * δ ≤ |C₁| * (1 + |C₁|) * δ := by
      have : |C₁| ≤ |C₁| * (1 + |C₁|) := le_mul_of_one_le_right (abs_nonneg _) (by linarith [abs_nonneg C₁])
      gcongr
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2]
  · have e1 : ∑ x, ((∑ m ∈ univ.filter (fun m => tgt m = some x), μ m : ℝ) : ℂ) * ω x
        = ω₀ * ∑ x, ∑ m ∈ univ.filter (fun m => tgt m = some x), (μ m : ℂ) * χ (bb m) (uu m) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      push_cast
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [hω m x (Finset.mem_filter.mp hm).2]; ring
    rw [e1, split, norm_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have n1 : ‖∑ m, (μ m : ℂ) * χ (bb m) (uu m)‖ ≤ |C₁| * (1 + |C₁|) * δ := by
      rw [fib]
      calc ‖∑ b, ∑ u ∈ Z, ((vol b / (VB * N) : ℝ) : ℂ) * χ b u‖
          ≤ ∑ b, ‖∑ u ∈ Z, ((vol b / (VB * N) : ℝ) : ℂ) * χ b u‖ := norm_sum_le _ _
        _ ≤ ∑ b, vol b / (VB * N) * (|C₁| * δ * (Z.card : ℝ)) := by
            refine Finset.sum_le_sum fun b _ => ?_
            rw [← Finset.mul_sum, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by have := hvol b; positivity)]
            refine mul_le_mul_of_nonneg_left ?_ (by have := hvol b; positivity)
            calc ‖∑ u ∈ Z, χ b u‖ ≤ C₁ * δ * (Z.card : ℝ) := hχZ b
              _ ≤ |C₁| * δ * (Z.card : ℝ) := by gcongr; exact le_abs_self _
        _ = |C₁| * δ * ((Z.card : ℝ) / N) := by rw [volsum]; ring
        _ ≤ |C₁| * δ * (1 + |C₁|) := by gcongr
        _ = _ := by ring
    have n2 : ‖∑ m ∈ univ.filter (fun m => tgt m = none), (μ m : ℂ) * χ (bb m) (uu m)‖ ≤ 2 * |C₂| * δ := by
      calc _ ≤ ∑ m ∈ univ.filter (fun m => tgt m = none), ‖(μ m : ℂ) * χ (bb m) (uu m)‖ := norm_sum_le _ _
        _ = ∑ m ∈ univ.filter (fun m => tgt m = none), μ m := by
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [norm_mul, hχ1, mul_one, Complex.norm_real, Real.norm_of_nonneg (hμ m)]
        _ ≤ _ := hL
    calc _ ≤ ‖∑ m, (μ m : ℂ) * χ (bb m) (uu m)‖
          + ‖∑ m ∈ univ.filter (fun m => tgt m = none), (μ m : ℂ) * χ (bb m) (uu m)‖ := norm_sub_le _ _
      _ ≤ |C₁| * (1 + |C₁|) * δ + 2 * |C₂| * δ := add_le_add n1 n2
      _ = _ := by ring

/- English proof (translation)
Introduce `E _ _ V _ _ h O abelian₂ hO hL hI`. Set `iS : StarRing O` to `{ star := fun a => ⟨star a.1, hO a.1 a.2⟩ star_involutive := fun a => Subtype.ext (star_star a.1) star_mul := fun a b => Subtype.ext (star_mul a.1 b.1) star_add := fun a b => Subtype.ext (star_add a.1 b.1) }`. Set `iM : Module O abelian₂` to `{ smul := fun a v => ⟨a.1 • v.1, hL a.1 a.2 v.1 v.2⟩ one_smul := fun v => Subtype.ext (one_smul E v.1) mul_smul := fun a b v => Subtype.ext (mul_smul a.1 b.1 v.1) smul_zero := fun a => Subtype.ext (smul_zero a.1) smul_add := fun a v w => Subtype.ext (smul_add a.1 v.1 w.1) add_smu …`. Set `h' : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O` to `LinearMap.mk₂'ₛₗ (RingHom.id O) (starRingEnd O) (fun v w => ⟨h v.1 w.1, hI v.1 v.2 w.1 w.2⟩) (fun a b c => Subtype.ext (by simp)) (fun c a b => Subtype.ext (by show h (c.1 • a.1) b.1 = c.1 * h a.1 b.1 simp)) (fun a b c => Subtype.ext (by simp)) (fun c a b => Subtype.ext (by show …`. Simplify using `[starRingEnd_apply]))`.

Use `⟨O, inferInstance, iS, abelian₂, inferInstance, iM, h', O.subtype, abelian₂.subtype, ?_⟩` and prove the remaining obligations. Conclude with `{ io_inj := Subtype.coe_injective io_range := fun c => ⟨fun hc => ⟨⟨c, hc⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩ io_star := fun _ => rfl j_inj := Subtype.coe_injective j_range := fun v => ⟨fun hv => ⟨⟨v, hv⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩ j_smul := fun _ _ => rfl form := fun _ _ => rf …`.
-/
theorem bridgeExists : BridgeExists := by
  intro E _ _ V _ _ h O abelian₂ hO hL hI
  let iS : StarRing O :=
    { star := fun a => ⟨star a.1, hO a.1 a.2⟩
      star_involutive := fun a => Subtype.ext (star_star a.1)
      star_mul := fun a b => Subtype.ext (star_mul a.1 b.1)
      star_add := fun a b => Subtype.ext (star_add a.1 b.1) }
  let iM : Module O abelian₂ :=
    { smul := fun a v => ⟨a.1 • v.1, hL a.1 a.2 v.1 v.2⟩
      one_smul := fun v => Subtype.ext (one_smul E v.1)
      mul_smul := fun a b v => Subtype.ext (mul_smul a.1 b.1 v.1)
      smul_zero := fun a => Subtype.ext (smul_zero a.1)
      smul_add := fun a v w => Subtype.ext (smul_add a.1 v.1 w.1)
      add_smul := fun a b v => Subtype.ext (add_smul a.1 b.1 v.1)
      zero_smul := fun v => Subtype.ext (zero_smul E v.1) }
  let h' : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O :=
    LinearMap.mk₂'ₛₗ (RingHom.id O) (starRingEnd O) (fun v w => ⟨h v.1 w.1, hI v.1 v.2 w.1 w.2⟩)
      (fun a b c => Subtype.ext (by simp))
      (fun c a b => Subtype.ext (by
        show h (c.1 • a.1) b.1 = c.1 * h a.1 b.1
        simp))
      (fun a b c => Subtype.ext (by simp))
      (fun c a b => Subtype.ext (by
        show h a.1 (c.1 • b.1) = star c.1 * h a.1 b.1
        simp [starRingEnd_apply]))
  refine ⟨O, inferInstance, iS, abelian₂, inferInstance, iM, h', O.subtype, abelian₂.subtype, ?_⟩
  exact
    { io_inj := Subtype.coe_injective
      io_range := fun c => ⟨fun hc => ⟨⟨c, hc⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
      io_star := fun _ => rfl
      j_inj := Subtype.coe_injective
      j_range := fun v => ⟨fun hv => ⟨⟨v, hv⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
      j_smul := fun _ _ => rfl
      form := fun _ _ => rfl }

/- English proof (translation)
Introduce `E _ _ _ V _ _ h O abelian₂ O' Lam' _ _ _ _ h' io j hM hh n b hb hperf hdual`. Establish `hbi : ∀ i, b i ∈ abelian₂` using `fun i => (hb _).mpr fun k => by`. Rewrite using `[b.repr_self, Finsupp.single_apply]`. Use `split_ifs`. Conclude with `O.one_mem`.

Conclude with `O.zero_mem`. Use `choose b' hb' using fun i => (hM.j_range _).mp (hbi i)`. Establish `hco : ∀ v : Lam', ∀ i, ∃ a, io a = b.repr (j v) i` using `fun v i => (hM.io_range _).mp ((hb _).mp ((hM.j_range _).mpr ⟨v, rfl⟩) i)`. Use `choose co hcoe using hco`. Establish `jsum : ∀ c : Fin n → O', j (∑ i, c i • b' i) = ∑ i, io (c i) • b i`.

Introduce `c; rw [map_sum]; exact Finset.sum_congr rfl fun i _ => by rw [hM.j_smul, hb']`. Establish `hexp : ∀ v : Lam', v = ∑ i, co v i • b' i`. Introduce `v`. Apply `hM.j_inj` to reduce the goal to its premises. Rewrite using `[jsum]`.

Use `conv_lhs => rw [← b.sum_repr (j v)]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hcoe]`. Establish `hind : ∀ c : Fin n → O', (∑ i, c i • b' i) = 0 → ∀ i, c i = 0`. Introduce `c hc i`. Establish `h0 : ∑ i, io (c i) • b i = 0` using `by rw [← jsum, hc, map_zero]`.

Use `(Fintype.linearIndependent_iff.mp b.linearIndependent) (fun i => io (c i)) h0 i` as an intermediate fact. Conclude with `hM.io_inj (by rw [this, map_zero])`. Establish `hli : LinearIndependent O' b'` using `Fintype.linearIndependent_iff.mpr hind`. Establish `hsp : ⊤ ≤ Submodule.span O' (Set.range b')`. Introduce `v _`.

Rewrite using `[hexp v]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Set `B' : Module.Basis (Fin n) O' Lam'` to `Module.Basis.mk hli hsp`. Establish `: Nontrivial O'` using `⟨⟨0, 1, fun h01 => by`. Use `congrArg io h01` as an intermediate fact.

Rewrite `this` using `[map_zero, map_one]`. Conclude with `zero_ne_one this⟩⟩`. Use `⟨⟨?_, ?_⟩, Module.Free.of_basis B', Module.Finite.of_basis B', ?_⟩` and prove the remaining obligations. Introduce `v w`. Apply `hM.io_inj` to reduce the goal to its premises.

Rewrite using `[← hM.form, hh, hM.form, hM.io_star]`. Introduce `φ`. Take `⟨v, hv⟩` from `hperf (b.constr E (fun i => io (φ (b' i))))`. Establish `key : ∀ x : Lam', io (φ x) = h (j x) v`. Introduce `x`.

Rewrite using `[← hv]`. Use `conv_lhs => rw [hexp x]`. Use `conv_rhs => rw [hexp x, jsum]`. Simplify using `[map_sum]`. Establish `hvL : v ∈ abelian₂` using `hdual v fun w hw => by`.

Take `⟨x, rfl⟩` from `(hM.j_range _).mp hw`. Rewrite using `[← key]`. Conclude with `(hM.io_range _).mpr ⟨_, rfl⟩`. Take `⟨w, rfl⟩` from `(hM.j_range _).mp hvL`. Conclude with `⟨w, fun x => hM.io_inj (by rw [key, hM.form])⟩`.

Rewrite using `[Module.finrank_eq_card_basis B']`. Simplify using the standard rewrite rules.
-/
theorem bridgeSelfDual : BridgeSelfDual := by
  intro E _ _ _ V _ _ h O abelian₂ O' Lam' _ _ _ _ h' io j hM hh n b hb hperf hdual

  have hbi : ∀ i, b i ∈ abelian₂ := fun i => (hb _).mpr fun k => by
    rw [b.repr_self, Finsupp.single_apply]; split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  choose b' hb' using fun i => (hM.j_range _).mp (hbi i)
  have hco : ∀ v : Lam', ∀ i, ∃ a, io a = b.repr (j v) i := fun v i =>
    (hM.io_range _).mp ((hb _).mp ((hM.j_range _).mpr ⟨v, rfl⟩) i)
  choose co hcoe using hco
  have jsum : ∀ c : Fin n → O', j (∑ i, c i • b' i) = ∑ i, io (c i) • b i := by
    intro c; rw [map_sum]; exact Finset.sum_congr rfl fun i _ => by rw [hM.j_smul, hb']
  have hexp : ∀ v : Lam', v = ∑ i, co v i • b' i := by
    intro v
    apply hM.j_inj
    rw [jsum]
    conv_lhs => rw [← b.sum_repr (j v)]
    exact Finset.sum_congr rfl fun i _ => by rw [hcoe]
  have hind : ∀ c : Fin n → O', (∑ i, c i • b' i) = 0 → ∀ i, c i = 0 := by
    intro c hc i
    have h0 : ∑ i, io (c i) • b i = 0 := by rw [← jsum, hc, map_zero]
    have := (Fintype.linearIndependent_iff.mp b.linearIndependent) (fun i => io (c i)) h0 i
    exact hM.io_inj (by rw [this, map_zero])
  have hli : LinearIndependent O' b' := Fintype.linearIndependent_iff.mpr hind
  have hsp : ⊤ ≤ Submodule.span O' (Set.range b') := by
    intro v _
    rw [hexp v]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let B' : Module.Basis (Fin n) O' Lam' := Module.Basis.mk hli hsp
  have : Nontrivial O' := ⟨⟨0, 1, fun h01 => by
    have := congrArg io h01
    rw [map_zero, map_one] at this
    exact zero_ne_one this⟩⟩
  refine ⟨⟨?_, ?_⟩, Module.Free.of_basis B', Module.Finite.of_basis B', ?_⟩
  · intro v w
    apply hM.io_inj
    rw [← hM.form, hh, hM.form, hM.io_star]
  · intro φ
    obtain ⟨v, hv⟩ := hperf (b.constr E (fun i => io (φ (b' i))))
    have key : ∀ x : Lam', io (φ x) = h (j x) v := by
      intro x
      rw [← hv]
      conv_lhs => rw [hexp x]
      conv_rhs => rw [hexp x, jsum]
      simp [map_sum]
    have hvL : v ∈ abelian₂ := hdual v fun w hw => by
      obtain ⟨x, rfl⟩ := (hM.j_range _).mp hw
      rw [← key]; exact (hM.io_range _).mpr ⟨_, rfl⟩
    obtain ⟨w, rfl⟩ := (hM.j_range _).mp hvL
    exact ⟨w, fun x => hM.io_inj (by rw [key, hM.form])⟩
  · rw [Module.finrank_eq_card_basis B']; simp

/- English proof (translation)
Introduce `o O' Lam' _ _ _ _ _ _ _ _ _ _ h' E _ _ V _ _ h O abelian₂ io j hU hSD hM hh hunit hspan r e he heL hli hprim`. Establish `nd' : ∀ w' : Lam', (∀ v', h' v' w' = 0) → w' = 0`. Introduce `w' hw'`. Set `bs` to `Module.Free.chooseBasis O' Lam'`. Apply `bs.ext_elem` to reduce the goal to its premises.

Introduce `i`. Take `⟨W, hW⟩` from `hSD.2 (bs.coord i)`. Establish `h1 : bs.coord i w' = h' w' W` using `hW w'`. Establish `h2 : h' w' W = 0` using `by rw [hSD.1 W w', hw' W, star_zero]`. Establish `h3 : bs.repr w' i = 0` using `by rw [← Module.Basis.coord_apply, h1, h2]`.

Rewrite using `[h3]`. Simplify using the standard rewrite rules. Establish `nd : ∀ v, (∀ w, h w v = 0) → v = 0`. Introduce `v hv`. Take `⟨c, hc, hcv⟩` from `hspan v`.

Take `⟨v', hv'⟩` from `(hM.j_range _).mp hcv`. Establish `: v' = 0` using `nd' v' fun x' => hM.io_inj (by`. Rewrite using `[← hM.form, hv', map_zero]`. Simplify using `[hv])`. Rewrite `hv'` using `[this, map_zero]`.

Take `⟨u, hu⟩` from `hunit c hc`. Establish `: v = ((u⁻¹ : Eˣ) : E) • (io (algebraMap o O' c) • v)` using `by rw [← hu, smul_smul]; simp`. Rewrite using `[this, ← hv', smul_zero]`. Establish `uniq : ∀ c c' : Fin r → E, (∑ i, c i • e i) = (∑ i, c' i • e i) → ∀ i, c i = c' i`. Introduce `c c' hcc i`.

Establish `h0 : ∑ i, (c i - c' i) • e i = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, hcc, sub_self]`. Conclude with `sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 i)`. Establish `part1 : ∃ y : Fin r → V, (∀ k, y k ∈ abelian₂) ∧ ∀ i k, h (y k) (e i) = if i = k then 1 else 0`. Set `Z₁ : Submodule E V` to `Submodule.span E (Set.range e)`.

Set `S' : Submodule O' Lam'` to `{ carrier := {v | j v ∈ Z₁} add_mem' := fun {a b} ha hb => by show j (a + b) ∈ Z₁`. Rewrite using `[map_add]`. Conclude with `Z₁.add_mem ha hb`. Use the proof step `zero_mem' := by show j 0 ∈ Z₁`. Rewrite using `[map_zero]`.

Conclude with `Z₁.zero_mem`. Use the proof step `smul_mem' := fun a v hv => by show j (a • v) ∈ Z₁`. Rewrite using `[hM.j_smul]`. Conclude with `Z₁.smul_mem _ hv }`. Establish `hsat : Satur o S'`.

Introduce `c v hc hmem`. Establish `h1 : io (algebraMap o O' c) • j v ∈ Z₁` using `by rw [← hM.j_smul]; exact hmem`. Take `⟨u, hu⟩` from `hunit c hc`. Establish `h2 : j v = ((u⁻¹ : Eˣ) : E) • (io (algebraMap o O' c) • j v)`. Rewrite using `[← hu, smul_smul]`.

Simplify using the standard rewrite rules. Use `show j v ∈ Z₁`. Rewrite using `[h2]`. Conclude with `Z₁.smul_mem _ h1`. Establish `hex : ∀ v : S', ∃ a : Fin r → O', j v = ∑ i, io (a i) • e i`.

Introduce `v`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun E).mp v.2`. Establish `hcO` using `hprim c (by rw [hc]; exact (hM.j_range _).mpr ⟨v, rfl⟩)`. Use `choose a ha using fun i => (hM.io_range _).mp (hcO i)`. Conclude with `⟨a, by rw [← hc]; exact Finset.sum_congr rfl fun i _ => by rw [ha]⟩`.

Use `choose A hA using hex`. Establish `Auniq : ∀ (v : S') (a : Fin r → O'), j v = ∑ i, io (a i) • e i → ∀ i, A v i = a i`. Introduce `v a hva i`. Conclude with `hM.io_inj (uniq _ _ ((hA v).symm.trans hva) i)`. Set `φ : Fin r → S' →ₗ[O'] O'` to `fun k => { toFun := fun v => A v k map_add' := fun a b => Auniq (a + b) (fun i => A a i + A b i) (by show j (a.1 + b.1) = _`.

Rewrite using `[map_add, hA a, hA b, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_add, add_smul]) k`. Use the proof step `map_smul' := fun c a => Auniq (c • a) (fun i => c * A a i) (by show j (c • a.1) = _`. Rewrite using `[hM.j_smul, hA a, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_smul]) k }`.

Use `choose w hw using fun k => H o O' Lam' h' hU hSD S' hsat (φ k)`. Use `choose e' he' using fun i => (hM.j_range _).mp (heL i)`. Establish `he'S : ∀ i, e' i ∈ S'` using `fun i => by show j (e' i) ∈ Z₁`. Rewrite using `[he']`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`.

Use `⟨fun k => j (w k), fun k => (hM.j_range _).mpr ⟨_, rfl⟩, fun i k => ?_⟩` and prove the remaining obligations. Establish `h1 : A ⟨e' i, he'S i⟩ k = if i = k then 1 else 0` using `Auniq ⟨e' i, he'S i⟩ (fun l => if i = l then 1 else 0) (by show j (e' i) = _`. Rewrite using `[he']`. Simplify using `[apply_ite io]) k`. Establish `h2 : h' (e' i) (w k) = if i = k then 1 else 0`.

Rewrite using `[← h1]`. Conclude with `(hw k ⟨e' i, he'S i⟩).symm`. Establish `h3 : h (e i) (j (w k)) = if i = k then 1 else 0`. Apply the tactic sequence `rw [← he', hM.form, h2]; split_ifs <;> simp`. Apply the tactic sequence `rw [hh (e i) (j (w k)), h3]; split_ifs <;> simp`.

Use `⟨part1, ?_⟩` and prove the remaining obligations. Take `⟨y, hyL, hye⟩` from `part1`. Introduce `d hd hdO`. Set `Z : Submodule E V` to `{ carrier := {v | ∀ i, h v (e i) = 0} add_mem' := fun {a b} ha hb i => by show h (a + b) (e i) = 0`. Rewrite using `[map_add, LinearMap.add_apply, ha i, hb i, add_zero]`.

Use the proof step `zero_mem' := fun i => by show h 0 (e i) = 0`. Simplify using the standard rewrite rules. Use the proof step `smul_mem' := fun c v hv i => by show h (c • v) (e i) = 0`. Rewrite using `[map_smul, LinearMap.smul_apply, hv i, smul_zero] }`. Take `⟨l, hl, hlZ⟩` from `HV o O' Lam' h' E V h O abelian₂ io j hU hSD hM hunit hspan Z d (fun w hw hwZ => hdO w hw hwZ)`.

Use `set v := d - l with hv`. Use `set c : Fin r → E := fun i => star (h (y i) v) with hc`. Establish `hzero : v - ∑ i, c i • e i = 0`. Apply `nd` to reduce the goal to its premises. Introduce `w`.

Use `set w₀ := w - ∑ k, h w (e k) • y k with hw₀`. Establish `hw₀Z : w₀ ∈ Z`. Introduce `i`. Use `show h w₀ (e i) = 0`. Rewrite using `[hw₀, map_sub, LinearMap.sub_apply, map_sum, LinearMap.sum_apply]`.

Simplify using `[hye]`. Establish `e1 : w = w₀ + ∑ k, h w (e k) • y k` using `by rw [hw₀]; abel`. Establish `a1 : h w₀ (v - ∑ i, c i • e i) = 0`. Rewrite using `[map_sub, hlZ w₀ hw₀Z, map_sum]`. Establish `hz : ∀ i, h w₀ (e i) = 0` using `hw₀Z`.

Simplify using `[hz]`. Establish `a2 : ∀ k, h (y k) (v - ∑ i, c i • e i) = 0`. Introduce `k`. Rewrite using `[map_sub, map_sum]`. Simplify using `[hye, hc, starRingEnd_apply]`.

Rewrite using `[e1, map_add, LinearMap.add_apply, a1, map_sum, LinearMap.sum_apply]`. Simplify using `[a2]`. Establish `hdl : d = l + ∑ i, c i • e i`. Establish `: v = ∑ i, c i • e i` using `sub_eq_zero.mp hzero`. Rewrite using `[← this, hv]`.

Normalize the expressions using the abelian group laws. Use `⟨l, hl, fun i => ?_, c, hdl⟩` and prove the remaining obligations. Establish `: l = d - ∑ k, c k • e k` using `by rw [hdl]; abel`. Rewrite using `[this, map_sub, LinearMap.sub_apply, hd i, map_sum, LinearMap.sum_apply]`. Simplify using `[he]`.
-/
theorem sameTraceHyp (H : DualCap) (HV : DualCapV) : SameTraceHyp := by
  intro o O' Lam' _ _ _ _ _ _ _ _ _ _ h' E _ _ V _ _ h O abelian₂ io j hU hSD hM hh hunit hspan r e he heL hli hprim

  have nd' : ∀ w' : Lam', (∀ v', h' v' w' = 0) → w' = 0 := by
    intro w' hw'
    let bs := Module.Free.chooseBasis O' Lam'
    apply bs.ext_elem
    intro i
    obtain ⟨W, hW⟩ := hSD.2 (bs.coord i)
    have h1 : bs.coord i w' = h' w' W := hW w'
    have h2 : h' w' W = 0 := by rw [hSD.1 W w', hw' W, star_zero]
    have h3 : bs.repr w' i = 0 := by rw [← Module.Basis.coord_apply, h1, h2]
    rw [h3]; simp
  have nd : ∀ v, (∀ w, h w v = 0) → v = 0 := by
    intro v hv
    obtain ⟨c, hc, hcv⟩ := hspan v
    obtain ⟨v', hv'⟩ := (hM.j_range _).mp hcv
    have : v' = 0 := nd' v' fun x' => hM.io_inj (by
      rw [← hM.form, hv', map_zero]; simp [hv])
    rw [this, map_zero] at hv'
    obtain ⟨u, hu⟩ := hunit c hc
    have : v = ((u⁻¹ : Eˣ) : E) • (io (algebraMap o O' c) • v) := by rw [← hu, smul_smul]; simp
    rw [this, ← hv', smul_zero]
  have uniq : ∀ c c' : Fin r → E, (∑ i, c i • e i) = (∑ i, c' i • e i) → ∀ i, c i = c' i := by
    intro c c' hcc i
    have h0 : ∑ i, (c i - c' i) • e i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, hcc, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 i)

  have part1 : ∃ y : Fin r → V, (∀ k, y k ∈ abelian₂) ∧ ∀ i k, h (y k) (e i) = if i = k then 1 else 0 := by
    let Z₁ : Submodule E V := Submodule.span E (Set.range e)
    let S' : Submodule O' Lam' :=
      { carrier := {v | j v ∈ Z₁}
        add_mem' := fun {a b} ha hb => by
          show j (a + b) ∈ Z₁
          rw [map_add]; exact Z₁.add_mem ha hb
        zero_mem' := by
          show j 0 ∈ Z₁
          rw [map_zero]; exact Z₁.zero_mem
        smul_mem' := fun a v hv => by
          show j (a • v) ∈ Z₁
          rw [hM.j_smul]; exact Z₁.smul_mem _ hv }
    have hsat : Satur o S' := by
      intro c v hc hmem
      have h1 : io (algebraMap o O' c) • j v ∈ Z₁ := by rw [← hM.j_smul]; exact hmem
      obtain ⟨u, hu⟩ := hunit c hc
      have h2 : j v = ((u⁻¹ : Eˣ) : E) • (io (algebraMap o O' c) • j v) := by
        rw [← hu, smul_smul]; simp
      show j v ∈ Z₁
      rw [h2]; exact Z₁.smul_mem _ h1
    have hex : ∀ v : S', ∃ a : Fin r → O', j v = ∑ i, io (a i) • e i := by
      intro v
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp v.2
      have hcO := hprim c (by rw [hc]; exact (hM.j_range _).mpr ⟨v, rfl⟩)
      choose a ha using fun i => (hM.io_range _).mp (hcO i)
      exact ⟨a, by rw [← hc]; exact Finset.sum_congr rfl fun i _ => by rw [ha]⟩
    choose A hA using hex
    have Auniq : ∀ (v : S') (a : Fin r → O'), j v = ∑ i, io (a i) • e i → ∀ i, A v i = a i := by
      intro v a hva i
      exact hM.io_inj (uniq _ _ ((hA v).symm.trans hva) i)
    let φ : Fin r → S' →ₗ[O'] O' := fun k =>
      { toFun := fun v => A v k
        map_add' := fun a b => Auniq (a + b) (fun i => A a i + A b i) (by
          show j (a.1 + b.1) = _
          rw [map_add, hA a, hA b, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by rw [map_add, add_smul]) k
        map_smul' := fun c a => Auniq (c • a) (fun i => c * A a i) (by
          show j (c • a.1) = _
          rw [hM.j_smul, hA a, Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_smul]) k }
    choose w hw using fun k => H o O' Lam' h' hU hSD S' hsat (φ k)
    choose e' he' using fun i => (hM.j_range _).mp (heL i)
    have he'S : ∀ i, e' i ∈ S' := fun i => by
      show j (e' i) ∈ Z₁
      rw [he']; exact Submodule.subset_span ⟨i, rfl⟩
    refine ⟨fun k => j (w k), fun k => (hM.j_range _).mpr ⟨_, rfl⟩, fun i k => ?_⟩
    have h1 : A ⟨e' i, he'S i⟩ k = if i = k then 1 else 0 :=
      Auniq ⟨e' i, he'S i⟩ (fun l => if i = l then 1 else 0) (by
        show j (e' i) = _
        rw [he']; simp [apply_ite io]) k
    have h2 : h' (e' i) (w k) = if i = k then 1 else 0 := by
      rw [← h1]; exact (hw k ⟨e' i, he'S i⟩).symm
    have h3 : h (e i) (j (w k)) = if i = k then 1 else 0 := by
      rw [← he', hM.form, h2]; split_ifs <;> simp
    rw [hh (e i) (j (w k)), h3]; split_ifs <;> simp
  refine ⟨part1, ?_⟩
  obtain ⟨y, hyL, hye⟩ := part1
  intro d hd hdO
  let Z : Submodule E V :=
    { carrier := {v | ∀ i, h v (e i) = 0}
      add_mem' := fun {a b} ha hb i => by
        show h (a + b) (e i) = 0
        rw [map_add, LinearMap.add_apply, ha i, hb i, add_zero]
      zero_mem' := fun i => by
        show h 0 (e i) = 0
        simp
      smul_mem' := fun c v hv i => by
        show h (c • v) (e i) = 0
        rw [map_smul, LinearMap.smul_apply, hv i, smul_zero] }
  obtain ⟨l, hl, hlZ⟩ := HV o O' Lam' h' E V h O abelian₂ io j hU hSD hM hunit hspan Z d (fun w hw hwZ => hdO w hw hwZ)
  set v := d - l with hv
  set c : Fin r → E := fun i => star (h (y i) v) with hc
  have hzero : v - ∑ i, c i • e i = 0 := by
    apply nd
    intro w
    set w₀ := w - ∑ k, h w (e k) • y k with hw₀
    have hw₀Z : w₀ ∈ Z := by
      intro i
      show h w₀ (e i) = 0
      rw [hw₀, map_sub, LinearMap.sub_apply, map_sum, LinearMap.sum_apply]
      simp [hye]
    have e1 : w = w₀ + ∑ k, h w (e k) • y k := by rw [hw₀]; abel
    have a1 : h w₀ (v - ∑ i, c i • e i) = 0 := by
      rw [map_sub, hlZ w₀ hw₀Z, map_sum]
      have hz : ∀ i, h w₀ (e i) = 0 := hw₀Z
      simp [hz]
    have a2 : ∀ k, h (y k) (v - ∑ i, c i • e i) = 0 := by
      intro k
      rw [map_sub, map_sum]
      simp [hye, hc, starRingEnd_apply]
    rw [e1, map_add, LinearMap.add_apply, a1, map_sum, LinearMap.sum_apply]
    simp [a2]
  have hdl : d = l + ∑ i, c i • e i := by
    have : v = ∑ i, c i • e i := sub_eq_zero.mp hzero
    rw [← this, hv]; abel
  refine ⟨l, hl, fun i => ?_, c, hdl⟩
  have : l = d - ∑ k, c k • e k := by rw [hdl]; abel
  rw [this, map_sub, LinearMap.sub_apply, hd i, map_sum, LinearMap.sum_apply]
  simp [he]

end Part2

/- English proof (translation)
The claim follows from `Part2.equalityNG`.
-/
theorem hermitian_count_equality : EqualityNG := Part2.equalityNG
/- English proof (translation)
The claim follows from `Part2.share_first_constant`.
-/
theorem shared_constant_formula : LocalDensityShareBound := Part2.share_first_constant
/- English proof (translation)
The claim follows from `Part2.tauLin`.
-/
theorem involution_map_linear : TauLin := Part2.tauLin
/- English proof (translation)
The claim follows from `Part2.leakProb`.
-/
theorem leakage_probability : LeakProb := Part2.leakProb
/- English proof (translation)
The claim follows from `Part2.rowSums`.
-/
theorem matrix_line_sums : RowSums := Part2.rowSums
/- English proof (translation)
The claim follows from `Part2.bridgeExists`.
-/
theorem self_dual_lattice_exists : BridgeExists := Part2.bridgeExists
/- English proof (translation)
The claim follows from `Part2.bridgeSelfDual`.
-/
theorem self_dual_lattice_extension : BridgeSelfDual := Part2.bridgeSelfDual
/- English proof (translation)
The claim follows from `Part2.thMParts span_character_ring`.
-/
theorem module_parts_decomposition : ThMParts := Part2.thMParts span_character_ring
/- English proof (translation)
The claim follows from `Part2.tauKer span_character_ring`.
-/
theorem involution_kernel : TauKer := Part2.tauKer span_character_ring
/- English proof (translation)
The claim follows from `Part2.tauHom involution_well_defined`.
-/
theorem involution_map_hom : TauHom := Part2.tauHom involution_well_defined
/- English proof (translation)
The claim follows from `Part2.moveAdm move_congruence Formalism.SL.Final.eichInv`.
-/
theorem move_admissible : MoveAdm := Part2.moveAdm move_congruence Formalism.SL.Final.eichInv
/- English proof (translation)
The claim follows from `Part2.movePerpX move_perpendicular`.
-/
theorem move_perpendicular_extended : MovePerpX := Part2.movePerpX move_perpendicular
/- English proof (translation)
The claim follows from `Part2.dualCapV dual_capacity_formula`.
-/
theorem dual_capacity_variant : DualCapV := Part2.dualCapV dual_capacity_formula
/- English proof (translation)
The claim follows from `Part2.assemblyNG2 type_cauchy_schwarz`.
-/
theorem hermitian_count_assembly_of_type : AssemblyNG2 := Part2.assemblyNG2 type_cauchy_schwarz
/- English proof (translation)
The claim follows from `Part2.sameTraceHyp dual_capacity_formula dual_capacity_variant`.
-/
theorem same_trace_hypothesis : SameTraceHyp := Part2.sameTraceHyp dual_capacity_formula dual_capacity_variant

section dvrcard
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]

/- English proof (translation)
Establish `h1` using `cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal o) (IsDiscreteValuationRing.not_a_field o) (i := i)`. Rewrite `h1` using `[hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]`. Establish `h2 : Submodule.cardQuot (Ideal.span {ϖ}) = q`. Rewrite using `[← hq, ← hϖ.maximalIdeal_eq]`. Both sides reduce to the same expression.

Rewrite `h1` using `[h2]`. Conclude with `h1`.
-/
lemma index_span_pow (ϖ : o) (hϖ : Irreducible ϖ) (q : ℕ)
    (hq : Nat.card (IsLocalRing.ResidueField o) = q) (i : ℕ) :
    (Ideal.span {ϖ ^ i}).toAddSubgroup.index = q ^ i := by
  have h1 := cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal o)
    (IsDiscreteValuationRing.not_a_field o) (i := i)
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at h1
  have h2 : Submodule.cardQuot (Ideal.span {ϖ}) = q := by
    rw [← hq, ← hϖ.maximalIdeal_eq]; rfl
  rw [h2] at h1
  exact h1

/- English proof (translation)
Establish `hker : f.ker = (Ideal.span {ϖ ^ i}).toAddSubgroup`. Use extensionality with `x`. Rewrite using `[AddMonoidHom.mem_ker, hk, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]`. Rewrite using `[← index_span_pow ϖ hϖ q hq i, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf]`. Conclude with `(Nat.card_congr (Equiv.Set.univ G)).symm`.
-/
lemma card_of_surj (ϖ : o) (hϖ : Irreducible ϖ) (q : ℕ)
    (hq : Nat.card (IsLocalRing.ResidueField o) = q) (i : ℕ) {G : Type} [AddCommGroup G]
    (f : o →+ G) (hf : Function.Surjective f) (hk : ∀ x, f x = 0 ↔ ϖ ^ i ∣ x) :
    Nat.card G = q ^ i := by
  have hker : f.ker = (Ideal.span {ϖ ^ i}).toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, hk, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
  rw [← index_span_pow ϖ hϖ q hq i, ← hker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.2 hf]
  exact (Nat.card_congr (Equiv.Set.univ G)).symm

end dvrcard

/- English proof (translation)
Introduce `o T _ _ _ _ _ _ ϖ red cond q a hϖ hq hq2 hsurj hker hcond`. Establish `hT : Fintype.card T = q ^ a`. Rewrite using `[← Nat.card_eq_fintype_card]`. Conclude with `card_of_surj ϖ hϖ q hq a red hsurj hker`. Establish `h0 : ∀ ψ, cond ψ = 0 ↔ ψ = 0`.

Introduce `ψ`. Rewrite using `[← Nat.le_zero, hcond]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `t`.

Take `⟨x, rfl⟩` from `hsurj t`. Simplify using `using h x`. Introduce and unpack `rfl x`. Simplify using the standard rewrite rules. Establish `ha : ∀ ψ, cond ψ ≤ a`.

Introduce `ψ`. Rewrite using `[hcond]`. Introduce `x`. Establish `: red (ϖ ^ a * x) = 0` using `(hker _).2 (dvd_mul_right _ _)`. Rewrite using `[this, AddChar.map_zero_eq_one]`.

Establish `hle : ∀ i, (univ.filter fun ψ : AddChar T ℂ => cond ψ ≤ i).card ≤ q ^ i`. Introduce `i`. Use `set N : AddSubgroup o := (Ideal.span {ϖ ^ i}).toAddSubgroup with hN`. Establish `hcardN : Nat.card (o ⧸ N) = q ^ i` using `index_span_pow ϖ hϖ q hq i`. Establish `: Finite (o ⧸ N)` using `Nat.finite_of_card_ne_zero (by rw [hcardN]; positivity)`.

Establish `: Fintype (o ⧸ N)` using `Fintype.ofFinite _`. Establish `hl : ∀ ψ : {ψ : AddChar T ℂ // cond ψ ≤ i}, ∀ x ∈ N, (ψ.1.compAddMonoidHom red).toAddMonoidHom x = 0`. Introduce `ψ x hx`. Rewrite `hx` using `[hN, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]`. Take `⟨y, rfl⟩` from `hx`.

Use `(hcond ψ.1 i).1 ψ.2 y` as an intermediate fact. Express the relevant statement in the definitionally equal form `Additive.ofMul (ψ.1 (red (ϖ ^ i * y))) = 0`. Rewrite using `[this]`. Both sides reduce to the same expression. Set `Φ : {ψ : AddChar T ℂ // cond ψ ≤ i} → AddChar (o ⧸ N) ℂ` to `fun ψ => AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift N _ (hl ψ))`.

Establish `hΦ : ∀ ψ x, Φ ψ (QuotientAddGroup.mk x) = ψ.1 (red x)` using `fun ψ x => rfl`. Establish `hinj : Function.Injective Φ`. Introduce `ψ ψ' h`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `t`.

Take `⟨x, rfl⟩` from `hsurj t`. Rewrite using `[← hΦ, ← hΦ, h]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨hT, h0, ha, fun i => ?_, fun i hi => ?_⟩` and prove the remaining obligations. Establish `h1 : (univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card ≤ q ^ i` using `(Finset.card_le_card (fun ψ hψ => by`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢`. Use the proof step `omega)).trans (hle i)`. Conclude with `h1` after adjusting the coercions. Establish `h1 : (univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card < q ^ i`. Use `lt_of_lt_of_le (Finset.card_lt_card ?_) (hle i)` and prove the remaining obligations.

Rewrite using `[Finset.ssubset_iff_of_subset (fun ψ hψ => by`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢`. Use the proof step `omega)]`. Use `⟨0, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`.

Rewrite using `[(h0 0).2 rfl]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[(h0 0).2 rfl]`. Use linear arithmetic over natural numbers and integers.

Conclude with `h1` after adjusting the coercions.
-/
theorem conditional_count_formula : CondCount := by
  intro o T _ _ _ _ _ _ ϖ red cond q a hϖ hq hq2 hsurj hker hcond
  classical
  have hT : Fintype.card T = q ^ a := by
    rw [← Nat.card_eq_fintype_card]; exact card_of_surj ϖ hϖ q hq a red hsurj hker
  have h0 : ∀ ψ, cond ψ = 0 ↔ ψ = 0 := by
    intro ψ
    rw [← Nat.le_zero, hcond]
    constructor
    · intro h
      ext t
      obtain ⟨x, rfl⟩ := hsurj t
      simpa using h x
    · rintro rfl x; simp
  have ha : ∀ ψ, cond ψ ≤ a := by
    intro ψ
    rw [hcond]
    intro x
    have : red (ϖ ^ a * x) = 0 := (hker _).2 (dvd_mul_right _ _)
    rw [this, AddChar.map_zero_eq_one]
  have hle : ∀ i, (univ.filter fun ψ : AddChar T ℂ => cond ψ ≤ i).card ≤ q ^ i := by
    intro i
    set N : AddSubgroup o := (Ideal.span {ϖ ^ i}).toAddSubgroup with hN
    have hcardN : Nat.card (o ⧸ N) = q ^ i := index_span_pow ϖ hϖ q hq i
    have : Finite (o ⧸ N) := Nat.finite_of_card_ne_zero (by rw [hcardN]; positivity)
    have : Fintype (o ⧸ N) := Fintype.ofFinite _
    have hl : ∀ ψ : {ψ : AddChar T ℂ // cond ψ ≤ i}, ∀ x ∈ N,
        (ψ.1.compAddMonoidHom red).toAddMonoidHom x = 0 := by
      intro ψ x hx
      rw [hN, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton] at hx
      obtain ⟨y, rfl⟩ := hx
      have := (hcond ψ.1 i).1 ψ.2 y
      change Additive.ofMul (ψ.1 (red (ϖ ^ i * y))) = 0
      rw [this]; rfl
    let Φ : {ψ : AddChar T ℂ // cond ψ ≤ i} → AddChar (o ⧸ N) ℂ := fun ψ =>
      AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift N _ (hl ψ))
    have hΦ : ∀ ψ x, Φ ψ (QuotientAddGroup.mk x) = ψ.1 (red x) := fun ψ x => rfl
    have hinj : Function.Injective Φ := by
      intro ψ ψ' h
      apply Subtype.ext
      ext t
      obtain ⟨x, rfl⟩ := hsurj t
      rw [← hΦ, ← hΦ, h]
    calc (univ.filter fun ψ : AddChar T ℂ => cond ψ ≤ i).card
        = Fintype.card {ψ : AddChar T ℂ // cond ψ ≤ i} := (Fintype.card_subtype _).symm
      _ ≤ Fintype.card (AddChar (o ⧸ N) ℂ) := Fintype.card_le_of_injective Φ hinj
      _ = Fintype.card (o ⧸ N) := AddChar.card_eq
      _ = q ^ i := by rw [← Nat.card_eq_fintype_card, hcardN]
  refine ⟨hT, h0, ha, fun i => ?_, fun i hi => ?_⟩
  · have h1 : (univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card ≤ q ^ i :=
      (Finset.card_le_card (fun ψ hψ => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢; omega)).trans (hle i)
    exact_mod_cast h1
  · have h1 : (univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card < q ^ i := by
      refine lt_of_lt_of_le (Finset.card_lt_card ?_) (hle i)
      rw [Finset.ssubset_iff_of_subset (fun ψ hψ => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢; omega)]
      refine ⟨0, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [(h0 0).2 rfl]; omega
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [(h0 0).2 rfl]; omega
    exact_mod_cast h1

section count
variable {F : Type} [Field F] [Fintype F]

/- English proof (translation)
Establish `h1 : M.rank = j` using `by simpa using hM.rank_matrix`. Establish `h2 : LinearMap.range M.mulVecLin = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[← Matrix.rank, h1]`. Simplify using the standard rewrite rules.

Introduce `y`. Establish `: y ∈ LinearMap.range M.mulVecLin` using `by rw [h2]; trivial`. Take `⟨x, hx⟩` from `this`. Conclude with `⟨x, hx⟩`.
-/
lemma mulVec_surj {j n : ℕ} (M : Matrix (Fin j) (Fin n) F) (hM : LinearIndependent F M.row) :
    Function.Surjective M.mulVec := by
  have h1 : M.rank = j := by simpa using hM.rank_matrix
  have h2 : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, h1]; simp
  intro y
  have : y ∈ LinearMap.range M.mulVecLin := by rw [h2]; trivial
  obtain ⟨x, hx⟩ := this
  exact ⟨x, hx⟩

/- English proof (translation)
Establish `hs` using `mulVec_surj M hM`. Establish `heq : ∀ g', (univ.filter fun y : Fin n → F => M.mulVec y = g').card = (univ.filter fun y : Fin n → F => M.mulVec y = g).card` using `fun g' => AddMonoidHom.card_fiber_eq_of_mem_range M.mulVecLin.toAddMonoidHom (hs g') (hs g)`. Establish `h1` using `Finset.card_eq_sum_card_fiberwise (f := M.mulVec) (s := (univ : Finset (Fin n → F))) (t := (univ : Finset (Fin j → F))) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))`. Simplify using `only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fun, Fintype.card_fin] at h1`. Rewrite using `[h1, mul_comm]`.
-/
lemma fiber_card [DecidableEq F] {j n : ℕ} (M : Matrix (Fin j) (Fin n) F)
    (hM : LinearIndependent F M.row) (g : Fin j → F) :
    (univ.filter fun y : Fin n → F => M.mulVec y = g).card * Fintype.card F ^ j
      = Fintype.card F ^ n := by
  have hs := mulVec_surj M hM
  have heq : ∀ g', (univ.filter fun y : Fin n → F => M.mulVec y = g').card
      = (univ.filter fun y : Fin n → F => M.mulVec y = g).card := fun g' =>
    AddMonoidHom.card_fiber_eq_of_mem_range M.mulVecLin.toAddMonoidHom (hs g') (hs g)
  have h1 := Finset.card_eq_sum_card_fiberwise (f := M.mulVec) (s := (univ : Finset (Fin n → F)))
    (t := (univ : Finset (Fin j → F))) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fun, Fintype.card_fin] at h1
  rw [h1, mul_comm]

/- English proof (translation)
Establish `h1 : ((Fintype.piFinset Fs).filter fun Y => ∑ j, lam j • Y j = 0).card ≤ (Fintype.piFinset (Function.update Fs j0 {0})).card`. Use `Finset.card_le_card_of_injOn (fun Y => Function.update Y j0 0) ?_ ?_` and prove the remaining obligations. Introduce `Y hY`. Establish `hY'` using `Fintype.mem_piFinset.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hY)).1`. Rewrite using `[Finset.mem_coe, Fintype.mem_piFinset]`.

Introduce `j`. Distinguish the cases in `hj : j = j0`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `only [Function.update_of_ne hj]`.

Conclude with `hY' j`. Introduce `Y hY Y' hY' hYY`. Establish `e1` using `(Finset.mem_filter.1 (Finset.mem_coe.1 hY)).2`. Establish `e2` using `(Finset.mem_filter.1 (Finset.mem_coe.1 hY')).2`. Establish `hne : ∀ j, j ≠ j0 → Y j = Y' j`.

Introduce `j hj`. Use `congrFun hYY j` as an intermediate fact. Simplify `this` using `only [Function.update_of_ne hj]`. Establish `e3 : ∑ j, lam j • (Y j - Y' j) = 0`. Simplify using `only [smul_sub, Finset.sum_sub_distrib, e1, e2, sub_self]`.

Rewrite `e3` using `[Finset.sum_eq_single j0 (fun j _ hj => by rw [hne j hj, sub_self, smul_zero]) (fun h => absurd (Finset.mem_univ _) h)]`. Establish `e4 : Y j0 = Y' j0`. Break down `smul_eq_zero.1 e3 with h | h` into its components or cases. Conclude with `absurd h hj0`. Conclude with `sub_eq_zero.1 h`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = j0`. Rewrite using `[hj]`. Conclude with `e4`. Conclude with `hne j hj`.

Establish `h2 : (Fintype.piFinset (Function.update Fs j0 {0})).card * c = c ^ m`. Rewrite using `[Fintype.card_piFinset, ← Finset.mul_prod_erase univ _ (Finset.mem_univ j0)]`. Establish `h3 : ∏ j ∈ univ.erase j0, (Function.update Fs j0 {0} j).card = c ^ (m - 1)`. Rewrite using `[Finset.prod_congr rfl (fun j hj => by`. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hj), hc] : ∀ j ∈ univ.erase j0, (Function.update Fs j0 {0} j).card = c)]`.

Simplify using the standard rewrite rules. Rewrite using `[h3]`. Simplify using `only [Function.update_self, Finset.card_singleton, one_mul]`. Establish `: 1 ≤ m` using `by have := j0.2; omega`. Rewrite using `[← pow_succ]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation.
-/
lemma dep_one [DecidableEq F] {m n : ℕ} (Fs : Fin m → Finset (Fin n → F)) (c : ℕ)
    (hc : ∀ j, (Fs j).card = c) (lam : Fin m → F) (j0 : Fin m) (hj0 : lam j0 ≠ 0) :
    ((Fintype.piFinset Fs).filter fun Y => ∑ j, lam j • Y j = 0).card * c ≤ c ^ m := by
  have h1 : ((Fintype.piFinset Fs).filter fun Y => ∑ j, lam j • Y j = 0).card
      ≤ (Fintype.piFinset (Function.update Fs j0 {0})).card := by
    refine Finset.card_le_card_of_injOn (fun Y => Function.update Y j0 0) ?_ ?_
    · intro Y hY
      have hY' := Fintype.mem_piFinset.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hY)).1
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro j
      by_cases hj : j = j0
      · subst hj; simp
      · simp only [Function.update_of_ne hj]; exact hY' j
    · intro Y hY Y' hY' hYY
      have e1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hY)).2
      have e2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hY')).2
      have hne : ∀ j, j ≠ j0 → Y j = Y' j := by
        intro j hj
        have := congrFun hYY j
        simpa only [Function.update_of_ne hj] using this
      have e3 : ∑ j, lam j • (Y j - Y' j) = 0 := by
        simp only [smul_sub, Finset.sum_sub_distrib, e1, e2, sub_self]
      rw [Finset.sum_eq_single j0 (fun j _ hj => by rw [hne j hj, sub_self, smul_zero])
        (fun h => absurd (Finset.mem_univ _) h)] at e3
      have e4 : Y j0 = Y' j0 := by
        rcases smul_eq_zero.1 e3 with h | h
        · exact absurd h hj0
        · exact sub_eq_zero.1 h
      funext j
      by_cases hj : j = j0
      · rw [hj]; exact e4
      · exact hne j hj
  have h2 : (Fintype.piFinset (Function.update Fs j0 {0})).card * c = c ^ m := by
    rw [Fintype.card_piFinset, ← Finset.mul_prod_erase univ _ (Finset.mem_univ j0)]
    have h3 : ∏ j ∈ univ.erase j0, (Function.update Fs j0 {0} j).card = c ^ (m - 1) := by
      rw [Finset.prod_congr rfl (fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), hc] :
          ∀ j ∈ univ.erase j0, (Function.update Fs j0 {0} j).card = c)]
      simp
    rw [h3]
    simp only [Function.update_self, Finset.card_singleton, one_mul]
    have : 1 ≤ m := by have := j0.2; omega
    rw [← pow_succ]; congr 1; omega
  calc _ ≤ (Fintype.piFinset (Function.update Fs j0 {0})).card * c := Nat.mul_le_mul_right _ h1
    _ = _ := h2

/- English proof (translation)
Establish `hsub : ((Fintype.piFinset Fs).filter fun Y => ¬ LinearIndependent F Y) ⊆ (univ.filter fun lam : Fin m → F => lam ≠ 0).biUnion fun lam => (Fintype.piFinset Fs).filter fun Y => ∑ j, lam j • Y j = 0`. Introduce `Y hY`. Take `⟨hY1, hY2⟩` from `Finset.mem_filter.1 hY`. Take `⟨lam, hl, i, hi⟩` from `Fintype.not_linearIndependent_iff.1 hY2`. Rewrite using `[Finset.mem_biUnion]`.

Use `⟨lam, ?_, Finset.mem_filter.2 ⟨hY1, hl⟩⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Introduce `h; exact hi (by rw [h]; rfl)`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun lam hl => ?_` and prove the remaining obligations.

Establish `hl' : lam ≠ 0` using `(Finset.mem_filter.1 hl).2`. Take `⟨j0, hj0⟩` from `Function.ne_iff.1 hl'`. Conclude with `dep_one Fs c hc lam j0 hj0`. Use `_ = (univ.filter (fun lam : Fin m → F => lam ≠ 0)).card * c ^ m := by`. Rewrite using `[Finset.sum_const, smul_eq_mul]`.

Use `_ ≤ _ := by`. Use `Nat.mul_le_mul_right _ ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
lemma dep_card [DecidableEq F] {m n : ℕ} (Fs : Fin m → Finset (Fin n → F)) (c : ℕ)
    (hc : ∀ j, (Fs j).card = c) [DecidablePred fun Y : Fin m → Fin n → F => LinearIndependent F Y] :
    ((Fintype.piFinset Fs).filter fun Y => ¬ LinearIndependent F Y).card * c
      ≤ Fintype.card F ^ m * c ^ m := by
  have hsub : ((Fintype.piFinset Fs).filter fun Y => ¬ LinearIndependent F Y)
      ⊆ (univ.filter fun lam : Fin m → F => lam ≠ 0).biUnion
          fun lam => (Fintype.piFinset Fs).filter fun Y => ∑ j, lam j • Y j = 0 := by
    intro Y hY
    obtain ⟨hY1, hY2⟩ := Finset.mem_filter.1 hY
    obtain ⟨lam, hl, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hY2
    rw [Finset.mem_biUnion]
    refine ⟨lam, ?_, Finset.mem_filter.2 ⟨hY1, hl⟩⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro h; exact hi (by rw [h]; rfl)
  calc _ ≤ (∑ lam ∈ univ.filter (fun lam : Fin m → F => lam ≠ 0),
        ((Fintype.piFinset Fs).filter fun Y => ∑ j, lam j • Y j = 0).card) * c :=
        Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
    _ = ∑ lam ∈ univ.filter (fun lam : Fin m → F => lam ≠ 0),
        ((Fintype.piFinset Fs).filter fun Y => ∑ j, lam j • Y j = 0).card * c := Finset.sum_mul _ _ _
    _ ≤ ∑ lam ∈ univ.filter (fun lam : Fin m → F => lam ≠ 0), c ^ m := by
        refine Finset.sum_le_sum fun lam hl => ?_
        have hl' : lam ≠ 0 := (Finset.mem_filter.1 hl).2
        obtain ⟨j0, hj0⟩ := Function.ne_iff.1 hl'
        exact dep_one Fs c hc lam j0 hj0
    _ = (univ.filter (fun lam : Fin m → F => lam ≠ 0)).card * c ^ m := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := by
        refine Nat.mul_le_mul_right _ ?_
        calc _ ≤ (univ : Finset (Fin m → F)).card := Finset.card_filter_le _ _
          _ = _ := by simp

/- English proof (translation)
Establish `htot : (Fintype.piFinset Fs).card = c ^ m`. Rewrite using `[Fintype.card_piFinset]`. Simplify using `[hc]`. Establish `hsplit` using `Finset.card_filter_add_card_filter_not (s := Fintype.piFinset Fs) (fun Y => LinearIndependent F Y)`. Establish `hdep` using `dep_card Fs c hc`.

Establish `hdepR : (((Fintype.piFinset Fs).filter fun Y => ¬ LinearIndependent F Y).card : ℝ) ≤ (Fintype.card F : ℝ) ^ m * (c : ℝ) ^ m / c`. Rewrite using `[le_div_iff₀ (by exact_mod_cast hc0)]`. Conclude with `hdep` after adjusting the coercions. Establish `hsR : (((Fintype.piFinset Fs).filter fun Y => LinearIndependent F Y).card : ℝ) + (((Fintype.piFinset Fs).filter fun Y => ¬ LinearIndependent F Y).card : ℝ) = (c : ℝ) ^ m`. Rewrite `hsplit` using `[htot]`.

Conclude with `hsplit` after adjusting the coercions. Prove the components needed by the constructor for the conclusion. Establish `: (0 : ℝ) ≤ (((Fintype.piFinset Fs).filter fun Y => ¬ LinearIndependent F Y).card : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma li_count [DecidableEq F] {m n : ℕ} (Fs : Fin m → Finset (Fin n → F)) (c : ℕ)
    (hc : ∀ j, (Fs j).card = c) (hc0 : 0 < c)
    [DecidablePred fun Y : Fin m → Fin n → F => LinearIndependent F Y] :
    (((Fintype.piFinset Fs).filter fun Y => LinearIndependent F Y).card : ℝ) ≤ (c : ℝ) ^ m ∧
    (c : ℝ) ^ m - (Fintype.card F : ℝ) ^ m * (c : ℝ) ^ m / c
      ≤ (((Fintype.piFinset Fs).filter fun Y => LinearIndependent F Y).card : ℝ) := by
  have htot : (Fintype.piFinset Fs).card = c ^ m := by
    rw [Fintype.card_piFinset]; simp [hc]
  have hsplit := Finset.card_filter_add_card_filter_not (s := Fintype.piFinset Fs)
    (fun Y => LinearIndependent F Y)
  have hdep := dep_card Fs c hc
  have hdepR : (((Fintype.piFinset Fs).filter fun Y => ¬ LinearIndependent F Y).card : ℝ)
      ≤ (Fintype.card F : ℝ) ^ m * (c : ℝ) ^ m / c := by
    rw [le_div_iff₀ (by exact_mod_cast hc0)]
    exact_mod_cast hdep
  have hsR : (((Fintype.piFinset Fs).filter fun Y => LinearIndependent F Y).card : ℝ)
      + (((Fintype.piFinset Fs).filter fun Y => ¬ LinearIndependent F Y).card : ℝ) = (c : ℝ) ^ m := by
    rw [htot] at hsplit
    exact_mod_cast hsplit
  constructor
  · have : (0 : ℝ) ≤ (((Fintype.piFinset Fs).filter fun Y => ¬ LinearIndependent F Y).card : ℝ) :=
      Nat.cast_nonneg _
    linarith
  · linarith

end count

/- English proof (translation)
Establish `hQ0 : 0 < Q` using `by linarith`. Establish `hQm : 0 < Q ^ m` using `by positivity`. Establish `hQn : 0 < Q ^ n` using `by positivity`. Establish `hc0 : 0 < c`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Establish `: c * Q ^ m ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg h hQm.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcm : 0 < c ^ m` using `by positivity`. Establish `hA : 0 < (Q ^ n) ^ m` using `by positivity`.

Establish `hmain : Q ^ (2 * n * m) / Q ^ (m ^ 2) = (Q ^ n) ^ m * c ^ m`. Rewrite using `[div_eq_iff (by positivity)]`. Establish `: c ^ m * Q ^ (m ^ 2) = (Q ^ n) ^ m`. Rewrite using `[← hc, mul_pow, ← pow_mul, sq]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← pow_mul, ← pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [← this]; ring`. Establish `h8 : (8 : ℝ) ≤ Q ^ 3`.

Combine the equalities or inequalities in the displayed calculation. Establish `e1 : Q ^ m / Q ^ n ≤ 1 / 8`. Rewrite using `[div_le_iff₀ hQn]`. Establish `: Q ^ n = Q ^ m * Q ^ (n - m)` using `by rw [← pow_add]; congr 1; omega`. Establish `h3 : Q ^ 3 ≤ Q ^ (n - m)` using `pow_le_pow_right₀ (by linarith) (by omega)`.

Rewrite using `[this]`. Use the polynomial consequences of the given equalities and inequalities. Establish `e2 : Q ^ m / c ≤ 1 / 8`. Rewrite using `[div_le_iff₀ hc0]`. Establish `h4 : Q ^ n = Q ^ m * Q ^ m * Q ^ (n - 2 * m)`.

Rewrite using `[← pow_add, ← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `h3 : Q ^ 3 ≤ Q ^ (n - 2 * m)` using `pow_le_pow_right₀ (by linarith) (by omega)`. Establish `h5 : c = Q ^ m * Q ^ (n - 2 * m)`.

Establish `: c * Q ^ m = (Q ^ m * Q ^ (n - 2 * m)) * Q ^ m` using `by rw [hc, h4]; ring`. Conclude with `mul_right_cancel₀ hQm.ne' this`. Rewrite using `[h5]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hmain]`.

Establish `hX2' : (Q ^ n) ^ m * (7 / 8) ≤ NX`. Establish `: Q ^ m * (Q ^ n) ^ m / Q ^ n = (Q ^ n) ^ m * (Q ^ m / Q ^ n)` using `by ring`. Rewrite `hX2` using `[this]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hY2 : c ^ m * (7 / 8) ≤ c ^ m - Q ^ m * c ^ m / c`.

Establish `: Q ^ m * c ^ m / c = c ^ m * (Q ^ m / c)` using `by ring`. Rewrite using `[this]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hNX0 : 0 ≤ NX` using `by nlinarith`. Prove the components needed by the constructor for the conclusion.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul hX2' hY2 (by positivity) hNX0` to reduce the goal to its premises. Use `_ ≤ tot := ht2`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma density_arith (Q : ℝ) (hQ : 2 ≤ Q) (n m : ℕ) (hn : 2 * m + 3 ≤ n) (c NX tot : ℝ)
    (hc : c * Q ^ m = Q ^ n)
    (hX1 : NX ≤ (Q ^ n) ^ m) (hX2 : (Q ^ n) ^ m - Q ^ m * (Q ^ n) ^ m / Q ^ n ≤ NX)
    (ht1 : tot ≤ NX * c ^ m) (ht2 : NX * (c ^ m - Q ^ m * c ^ m / c) ≤ tot) :
    Q ^ (2 * n * m) / Q ^ (m ^ 2) / 2 ≤ tot ∧ tot ≤ 2 * (Q ^ (2 * n * m) / Q ^ (m ^ 2)) := by
  have hQ0 : 0 < Q := by linarith
  have hQm : 0 < Q ^ m := by positivity
  have hQn : 0 < Q ^ n := by positivity
  have hc0 : 0 < c := by
    by_contra h
    push Not at h
    have : c * Q ^ m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hQm.le
    linarith
  have hcm : 0 < c ^ m := by positivity
  have hA : 0 < (Q ^ n) ^ m := by positivity
  have hmain : Q ^ (2 * n * m) / Q ^ (m ^ 2) = (Q ^ n) ^ m * c ^ m := by
    rw [div_eq_iff (by positivity)]
    have : c ^ m * Q ^ (m ^ 2) = (Q ^ n) ^ m := by
      rw [← hc, mul_pow, ← pow_mul, sq]
    calc Q ^ (2 * n * m) = (Q ^ n) ^ m * (Q ^ n) ^ m := by
          rw [← pow_mul, ← pow_add]; congr 1; ring
      _ = _ := by rw [← this]; ring
  have h8 : (8 : ℝ) ≤ Q ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ Q ^ 3 := by gcongr
  have e1 : Q ^ m / Q ^ n ≤ 1 / 8 := by
    rw [div_le_iff₀ hQn]
    have : Q ^ n = Q ^ m * Q ^ (n - m) := by rw [← pow_add]; congr 1; omega
    have h3 : Q ^ 3 ≤ Q ^ (n - m) := pow_le_pow_right₀ (by linarith) (by omega)
    rw [this]
    nlinarith
  have e2 : Q ^ m / c ≤ 1 / 8 := by
    rw [div_le_iff₀ hc0]
    have h4 : Q ^ n = Q ^ m * Q ^ m * Q ^ (n - 2 * m) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have h3 : Q ^ 3 ≤ Q ^ (n - 2 * m) := pow_le_pow_right₀ (by linarith) (by omega)
    have h5 : c = Q ^ m * Q ^ (n - 2 * m) := by
      have : c * Q ^ m = (Q ^ m * Q ^ (n - 2 * m)) * Q ^ m := by rw [hc, h4]; ring
      exact mul_right_cancel₀ hQm.ne' this
    rw [h5]
    nlinarith
  rw [hmain]
  have hX2' : (Q ^ n) ^ m * (7 / 8) ≤ NX := by
    have : Q ^ m * (Q ^ n) ^ m / Q ^ n = (Q ^ n) ^ m * (Q ^ m / Q ^ n) := by ring
    rw [this] at hX2
    nlinarith
  have hY2 : c ^ m * (7 / 8) ≤ c ^ m - Q ^ m * c ^ m / c := by
    have : Q ^ m * c ^ m / c = c ^ m * (Q ^ m / c) := by ring
    rw [this]
    nlinarith
  have hNX0 : 0 ≤ NX := by nlinarith
  constructor
  · calc (Q ^ n) ^ m * c ^ m / 2 ≤ ((Q ^ n) ^ m * (7 / 8)) * (c ^ m * (7 / 8)) := by nlinarith [mul_pos hA hcm]
      _ ≤ NX * (c ^ m - Q ^ m * c ^ m / c) := by
          apply mul_le_mul hX2' hY2 (by positivity) hNX0
      _ ≤ tot := ht2
  · calc tot ≤ NX * c ^ m := ht1
      _ ≤ (Q ^ n) ^ m * c ^ m := by gcongr
      _ ≤ _ := by nlinarith [mul_pos hA hcm]

/- English proof (translation)
Introduce `K _ _ n m Ph Gm hn hPh`. Establish `hq2 : (2 : ℝ) ≤ (Fintype.card K : ℝ)` using `by exact_mod_cast Fintype.one_lt_card (α := K)`. Establish `hqpos : 0 < Fintype.card K` using `Fintype.card_pos`. Set `MX : (Fin m → Fin n → K) → Matrix (Fin m) (Fin n) K` to `fun X => (Matrix.of X) * Ph`. Establish `hcond : ∀ (X Y : Fin m → Fin n → K), (∀ i j, ∑ k, ∑ l, X i k * Ph k l * Y j l = Gm i j) ↔ ∀ j, (MX X).mulVec (Y j) = fun i => Gm i j`.

Introduce `X Y`. Establish `: ∀ i j, ∑ k, ∑ l, X i k * Ph k l * Y j l = (MX X).mulVec (Y j) i`. Introduce `i j`. Simplify using `only [MX, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.

Simplify using `only [this]`. Prove the components needed by the constructor for the conclusion. Introduce `h j`. Use function extensionality and compare the values at `i`. Conclude with `h i j`.

Introduce `h i j`. Conclude with `congrFun (h j) i`. Establish `hrow : ∀ X : Fin m → Fin n → K, LinearIndependent K X → LinearIndependent K (MX X).row`. Introduce `X hX`. Establish `hinj : LinearMap.ker (Matrix.vecMulLinear Ph) = ⊥`.

Rewrite using `[LinearMap.ker_eq_bot]`. Introduce `x y hxy`. Establish `h1 : ∀ z : Fin n → K, Matrix.vecMul (Matrix.vecMul z Ph) Ph⁻¹ = z` using `fun z => by`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv Ph hPh, Matrix.vecMul_one]`. Rewrite using `[← h1 x, ← h1 y]`.

Conclude with `congrArg (fun z => Matrix.vecMul z Ph⁻¹) hxy`. Use `hX.map' (Matrix.vecMulLinear Ph) hinj` as an intermediate fact. Establish `heq : (MX X).row = ⇑(Matrix.vecMulLinear Ph) ∘ X`. Use function extensionality and compare the values at `i`. Use function extensionality and compare the values at `l`.

Simplify using `[MX, Matrix.row, Matrix.mul_apply, Matrix.vecMul, dotProduct]`. Rewrite using `[heq]`. Conclude with `this`. Take `⟨c, hc⟩ : ∃ c : ℕ, c * Fintype.card K ^ m = Fintype.card K ^ n` from `⟨Fintype.card K ^ (n - m), by rw [← pow_add]; congr 1; omega⟩`. Establish `hc0 : 0 < c`.

Break down `Nat.eq_zero_or_pos c with h | h` into its components or cases. Rewrite `hc` using `[h, zero_mul]`. Conclude with `absurd hc.symm (by positivity)`. Conclude with `h`. Set `NY : (Fin m → Fin n → K) → ℕ` to `fun X => (univ.filter fun Y : Fin m → Fin n → K => LinearIndependent K Y ∧ ∀ i j, ∑ k, ∑ l, X i k * Ph k l * Y j l = Gm i j).card`.

Establish `hNY : ∀ X, LinearIndependent K X → ((NY X : ℕ) : ℝ) ≤ (c : ℝ) ^ m ∧ (c : ℝ) ^ m - (Fintype.card K : ℝ) ^ m * (c : ℝ) ^ m / c ≤ ((NY X : ℕ) : ℝ)`. Introduce `X hX`. Set `Fs : Fin m → Finset (Fin n → K)` to `fun j => univ.filter fun y => (MX X).mulVec y = fun i => Gm i j`. Establish `hFs : ∀ j, (Fs j).card = c`. Introduce `j`.

Use `fiber_card (MX X) (hrow X hX) (fun i => Gm i j)` as an intermediate fact. Rewrite `this` using `[← hc]`. Conclude with `Nat.eq_of_mul_eq_mul_right (by positivity) this`. Establish `heq : (univ.filter fun Y : Fin m → Fin n → K => LinearIndependent K Y ∧ ∀ i j, ∑ k, ∑ l, X i k * Ph k l * Y j l = Gm i j) = (Fintype.piFinset Fs).filter fun Y => LinearIndependent K Y`. Use extensionality with `Y`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, Fs, hcond]`. Conclude with `and_comm`. Use `li_count Fs c hFs hc0` as an intermediate fact. Simplify using `only [NY, heq]`. Conclude with `this`.

Establish `hXcount` using `li_count (F := K) (m := m) (n := n) (fun _ => univ) (Fintype.card K ^ n) (fun _ => by simp) (by positivity)`. Establish `hpi : (Fintype.piFinset fun _ : Fin m => (univ : Finset (Fin n → K))) = univ` using `by ext; simp`. Rewrite `hXcount` using `[hpi]`. Establish `hset : ({XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) | LinearIndependent K XY.1 ∧ LinearIndependent K XY.2 ∧ ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph k l * XY.2 j l = Gm i j}.ncard : ℝ) = ∑ X ∈ univ.filter (fun X : Fin m → Fin n → K => LinearIndependent K X), ((NY X : ℕ) : ℝ)`. Establish `h1 : {XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) | LinearIndependent K XY.1 ∧ LinearIndependent K XY.2 ∧ ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph k l * XY.2 j l = Gm i j} = ↑(univ.filter fun XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) => LinearIndependent K XY.1 ∧ LinearIndependent …` using `by ext; simp`.

Rewrite using `[h1, Set.ncard_coe_finset, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_filter]`. Use `push_cast`. Use `Finset.sum_congr rfl fun X _ => ?_` and prove the remaining obligations. Distinguish the cases in `hX : LinearIndependent K X`. Simplify using `only [hX, true_and, if_true, NY, Finset.card_filter]`.

Use `push_cast`. Both sides reduce to the same expression. Simplify using `[hX]`. Rewrite using `[hset]`. Move the coercions through the operations in `at hXcount`.

Use `density_arith (Fintype.card K : ℝ) hq2 n m hn (c : ℝ) ((univ.filter (fun X : Fin m → Fin n → K => LinearIndependent K X)).card : ℝ) _ (by exact_mod_cast hc) hXcount.1 hXcount.2 ?_ ?_` and prove the remaining obligations. Rewrite using `[← nsmul_eq_mul]`. Conclude with `Finset.sum_le_card_nsmul _ _ _ fun X hX => (hNY X (Finset.mem_filter.1 hX).2).1`. Rewrite using `[← nsmul_eq_mul]`. Conclude with `Finset.card_nsmul_le_sum _ _ _ fun X hX => (hNY X (Finset.mem_filter.1 hX).2).2`.
-/
theorem primitive_density_split_form : PrimDensitySplitForm := by
  intro K _ _ n m Ph Gm hn hPh
  classical
  have hq2 : (2 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hqpos : 0 < Fintype.card K := Fintype.card_pos

  let MX : (Fin m → Fin n → K) → Matrix (Fin m) (Fin n) K := fun X => (Matrix.of X) * Ph
  have hcond : ∀ (X Y : Fin m → Fin n → K),
      (∀ i j, ∑ k, ∑ l, X i k * Ph k l * Y j l = Gm i j) ↔ ∀ j, (MX X).mulVec (Y j) = fun i => Gm i j := by
    intro X Y
    have : ∀ i j, ∑ k, ∑ l, X i k * Ph k l * Y j l = (MX X).mulVec (Y j) i := by
      intro i j
      simp only [MX, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
      exact Finset.sum_comm
    simp only [this]
    constructor
    · intro h j; funext i; exact h i j
    · intro h i j; exact congrFun (h j) i
  have hrow : ∀ X : Fin m → Fin n → K, LinearIndependent K X → LinearIndependent K (MX X).row := by
    intro X hX
    have hinj : LinearMap.ker (Matrix.vecMulLinear Ph) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      have h1 : ∀ z : Fin n → K, Matrix.vecMul (Matrix.vecMul z Ph) Ph⁻¹ = z := fun z => by
        rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv Ph hPh, Matrix.vecMul_one]
      rw [← h1 x, ← h1 y]
      exact congrArg (fun z => Matrix.vecMul z Ph⁻¹) hxy
    have := hX.map' (Matrix.vecMulLinear Ph) hinj
    have heq : (MX X).row = ⇑(Matrix.vecMulLinear Ph) ∘ X := by
      funext i
      funext l
      simp [MX, Matrix.row, Matrix.mul_apply, Matrix.vecMul, dotProduct]
    rw [heq]
    exact this
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c * Fintype.card K ^ m = Fintype.card K ^ n :=
    ⟨Fintype.card K ^ (n - m), by rw [← pow_add]; congr 1; omega⟩
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, zero_mul] at hc
      exact absurd hc.symm (by positivity)
    · exact h
  let NY : (Fin m → Fin n → K) → ℕ := fun X =>
    (univ.filter fun Y : Fin m → Fin n → K => LinearIndependent K Y ∧
      ∀ i j, ∑ k, ∑ l, X i k * Ph k l * Y j l = Gm i j).card
  have hNY : ∀ X, LinearIndependent K X → ((NY X : ℕ) : ℝ) ≤ (c : ℝ) ^ m ∧
      (c : ℝ) ^ m - (Fintype.card K : ℝ) ^ m * (c : ℝ) ^ m / c ≤ ((NY X : ℕ) : ℝ) := by
    intro X hX
    let Fs : Fin m → Finset (Fin n → K) := fun j => univ.filter fun y => (MX X).mulVec y = fun i => Gm i j
    have hFs : ∀ j, (Fs j).card = c := by
      intro j
      have := fiber_card (MX X) (hrow X hX) (fun i => Gm i j)
      rw [← hc] at this
      exact Nat.eq_of_mul_eq_mul_right (by positivity) this
    have heq : (univ.filter fun Y : Fin m → Fin n → K => LinearIndependent K Y ∧
        ∀ i j, ∑ k, ∑ l, X i k * Ph k l * Y j l = Gm i j)
        = (Fintype.piFinset Fs).filter fun Y => LinearIndependent K Y := by
      ext Y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, Fs, hcond]
      exact and_comm
    have := li_count Fs c hFs hc0
    simp only [NY, heq]
    exact this
  have hXcount := li_count (F := K) (m := m) (n := n) (fun _ => univ) (Fintype.card K ^ n)
    (fun _ => by simp) (by positivity)
  have hpi : (Fintype.piFinset fun _ : Fin m => (univ : Finset (Fin n → K))) = univ := by
    ext; simp
  rw [hpi] at hXcount
  have hset : ({XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) | LinearIndependent K XY.1 ∧
      LinearIndependent K XY.2 ∧ ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph k l * XY.2 j l = Gm i j}.ncard : ℝ)
      = ∑ X ∈ univ.filter (fun X : Fin m → Fin n → K => LinearIndependent K X), ((NY X : ℕ) : ℝ) := by
    have h1 : {XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) | LinearIndependent K XY.1 ∧
        LinearIndependent K XY.2 ∧ ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph k l * XY.2 j l = Gm i j}
        = ↑(univ.filter fun XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) => LinearIndependent K XY.1 ∧
        LinearIndependent K XY.2 ∧ ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph k l * XY.2 j l = Gm i j) := by
      ext; simp
    rw [h1, Set.ncard_coe_finset, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_filter]
    push_cast
    refine Finset.sum_congr rfl fun X _ => ?_
    by_cases hX : LinearIndependent K X
    · simp only [hX, true_and, if_true, NY, Finset.card_filter]
      push_cast
      rfl
    · simp [hX]
  rw [hset]
  push_cast at hXcount
  refine density_arith (Fintype.card K : ℝ) hq2 n m hn (c : ℝ)
    ((univ.filter (fun X : Fin m → Fin n → K => LinearIndependent K X)).card : ℝ) _
    (by exact_mod_cast hc) hXcount.1 hXcount.2 ?_ ?_
  · rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun X hX => (hNY X (Finset.mem_filter.1 hX).2).1
  · rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ fun X hX => (hNY X (Finset.mem_filter.1 hX).2).2

/- English proof (translation)
Introduce `K _ _ n m Gm hn`. Use `primitive_density_split_form K n m 1 Gm hn (by simp)` as an intermediate fact. Simplify `this` using `[Matrix.one_apply, mul_ite, ite_mul, Finset.sum_ite_eq]`.
-/
theorem primitive_density_split : PrimDensitySplit := by
  intro K _ _ n m Gm hn
  have := primitive_density_split_form K n m 1 Gm hn (by simp)
  simpa [Matrix.one_apply, mul_ite, ite_mul, Finset.sum_ite_eq] using this

section inert
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

/- English proof (translation)
The claim follows from `map_add (FiniteField.frobeniusAlgHom K L) x y`.
-/
lemma frob_add (x y : L) :
    (x + y) ^ Fintype.card K = x ^ Fintype.card K + y ^ Fintype.card K :=
  map_add (FiniteField.frobeniusAlgHom K L) x y

/- English proof (translation)
The claim follows from `map_sum (FiniteField.frobeniusAlgHom K L) f s`.
-/
lemma frob_sum {ι : Type} (s : Finset ι) (f : ι → L) :
    (∑ i ∈ s, f i) ^ Fintype.card K = ∑ i ∈ s, f i ^ Fintype.card K :=
  map_sum (FiniteField.frobeniusAlgHom K L) f s

/- English proof (translation)
Rewrite using `[← h2]`. Conclude with `Module.card_eq_pow_finrank`.
-/
lemma card_L (h2 : Module.finrank K L = 2) : Fintype.card L = Fintype.card K ^ 2 := by
  rw [← h2]; exact Module.card_eq_pow_finrank

/- English proof (translation)
Rewrite using `[← pow_mul, ← sq, ← card_L h2, FiniteField.pow_card]`.
-/
lemma frob_frob (h2 : Module.finrank K L = 2) (x : L) :
    (x ^ Fintype.card K) ^ Fintype.card K = x := by
  rw [← pow_mul, ← sq, ← card_L h2, FiniteField.pow_card]

@[reducible] def frobStar (h2 : Module.finrank K L = 2) : StarRing L where
  star x := x ^ Fintype.card K
  star_involutive := frob_frob h2
  star_mul x y := by rw [mul_pow, mul_comm]
  star_add := frob_add

/- English proof (translation)
Rewrite using `[FiniteField.algebraMap_trace_eq_sum_pow, h2, Finset.sum_range_succ, Finset.sum_range_one, Nat.card_eq_fintype_card]`. Simplify using the standard rewrite rules.
-/
lemma trace_eq (h2 : Module.finrank K L = 2) (z : L) :
    algebraMap K L (Algebra.trace K L z) = z + z ^ Fintype.card K := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow, h2, Finset.sum_range_succ, Finset.sum_range_one,
    Nat.card_eq_fintype_card]
  simp

/- English proof (translation)
Establish `: FiniteDimensional K L` using `Module.Finite.of_finite`. Conclude with `Algebra.trace_surjective K L`.
-/
lemma trace_surj : Function.Surjective (Algebra.trace K L) := by
  have : FiniteDimensional K L := Module.Finite.of_finite
  exact Algebra.trace_surjective K L

/- English proof (translation)
Set `ψ' : AddChar L ℂ` to `ψ.compAddMonoidHom (Algebra.trace K L).toAddMonoidHom`. Establish `h` using `@hermitian_gauss_sum_ring L _ _ (frobStar h2) n Ph ψ' φ hPh hφ hadd`. Establish `hY : Nat.card {y : L // ∀ c, ψ' (c * y) = 1} ≤ 1`. Rewrite using `[Finite.card_le_one_iff_subsingleton]`. Establish `h0 : ∀ y : {y : L // ∀ c, ψ' (c * y) = 1}, y.1 = 0`.

Introduce `y`. Assume the negation of the conclusion as `hy`. Apply `hψ` to reduce the goal to its premises. Use extensionality with `k`. Take `⟨z, rfl⟩` from `trace_surj (K := K) (L := L) k`.

Use `y.2 (z / y.1)` as an intermediate fact. Rewrite `this` using `[div_mul_cancel₀ _ hy]`. Rewrite using `[AddChar.zero_apply]`. Conclude with `this`. Conclude with `⟨fun y y' => Subtype.ext (by rw [h0 y, h0 y'])⟩`.

Establish `hY' : (Nat.card {y : L // ∀ c, ψ' (c * y) = 1} : ℝ) ^ n ≤ 1`. Apply `pow_le_one₀ (Nat.cast_nonneg _)` to reduce the goal to its premises. Conclude with `hY` after adjusting the coercions. Establish `h3 : ‖∑ u, φ u‖ ^ 2 ≤ ((Fintype.card K : ℝ) ^ n) ^ 2`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3`.
-/
lemma gauss_inert (h2 : Module.finrank K L = 2) (n : ℕ) (Ph : Matrix (Fin n) (Fin n) L)
    (hPh : IsUnit Ph.det) (ψ : AddChar K ℂ) (hψ : ψ ≠ 0) (φ : (Fin n → L) → ℂ)
    (hφ : ∀ u, ‖φ u‖ = 1)
    (hadd : ∀ u d, φ (u + d) = φ u * φ d *
      ψ (Algebra.trace K L (∑ i, ∑ j, u i * Ph i j * d j ^ Fintype.card K))) :
    ‖∑ u, φ u‖ ≤ (Fintype.card K : ℝ) ^ n := by
  let ψ' : AddChar L ℂ := ψ.compAddMonoidHom (Algebra.trace K L).toAddMonoidHom
  have h := @hermitian_gauss_sum_ring L _ _ (frobStar h2) n Ph ψ' φ hPh hφ hadd
  have hY : Nat.card {y : L // ∀ c, ψ' (c * y) = 1} ≤ 1 := by
    rw [Finite.card_le_one_iff_subsingleton]
    have h0 : ∀ y : {y : L // ∀ c, ψ' (c * y) = 1}, y.1 = 0 := by
      intro y
      by_contra hy
      apply hψ
      ext k
      obtain ⟨z, rfl⟩ := trace_surj (K := K) (L := L) k
      have := y.2 (z / y.1)
      rw [div_mul_cancel₀ _ hy] at this
      rw [AddChar.zero_apply]
      exact this
    exact ⟨fun y y' => Subtype.ext (by rw [h0 y, h0 y'])⟩
  have hY' : (Nat.card {y : L // ∀ c, ψ' (c * y) = 1} : ℝ) ^ n ≤ 1 := by
    apply pow_le_one₀ (Nat.cast_nonneg _)
    exact_mod_cast hY
  have h3 : ‖∑ u, φ u‖ ^ 2 ≤ ((Fintype.card K : ℝ) ^ n) ^ 2 := by
    calc _ ≤ _ := h
      _ ≤ (Fintype.card L : ℝ) ^ n * 1 := by gcongr
      _ = _ := by rw [card_L h2]; push_cast; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3

end inert

section inert2
variable (K : Type) {L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

def hB {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L) (x y : Fin n → L) : L :=
  ∑ k, ∑ l, x k * Ph k l * y l ^ Fintype.card K

def hMat {n j : ℕ} (Ph : Matrix (Fin n) (Fin n) L) (X : Fin j → Fin n → L) :
    Matrix (Fin j) (Fin n) L :=
  Matrix.of fun b k => ∑ l, Ph k l * X b l ^ Fintype.card K

variable {K}
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)

/- English proof (translation)
Simplify using `only [hB, Pi.add_apply, add_mul, Finset.sum_add_distrib]`.
-/
lemma hB_add_left (x d y : Fin n → L) : hB K Ph (x + d) y = hB K Ph x y + hB K Ph d y := by
  simp only [hB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hB, Pi.add_apply, frob_add, mul_add, Finset.sum_add_distrib]`.
-/
lemma hB_add_right (x y d : Fin n → L) : hB K Ph x (y + d) = hB K Ph x y + hB K Ph x d := by
  simp only [hB, Pi.add_apply, frob_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hB, frob_sum, mul_pow, frob_frob h2, ← hherm]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring`.
-/
lemma hB_conj (h2 : Module.finrank K L = 2) (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K)
    (x y : Fin n → L) : hB K Ph x y ^ Fintype.card K = hB K Ph y x := by
  simp only [hB, frob_sum, mul_pow, frob_frob h2, ← hherm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Simplify using `only [hB, hMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring`.
-/
lemma hB_mulVec {j : ℕ} (X : Fin j → Fin n → L) (x : Fin n → L) (b : Fin j) :
    hB K Ph x (X b) = (hMat K Ph X).mulVec x b := by
  simp only [hB, hMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Use `set w : Fin n → L := fun l => ∑ b, g b * X b l ^ Fintype.card K with hw`. Establish `h1 : Ph.mulVec w = 0`. Use function extensionality and compare the values at `k`.

Use `congrFun hg k` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Matrix.row, hMat, Matrix.of_apply, smul_eq_mul, Pi.zero_apply, Finset.mul_sum] at this`. Simplify using `only [Matrix.mulVec, dotProduct, hw, Finset.mul_sum, Pi.zero_apply]`. Rewrite using `[Finset.sum_comm, ← this]`. Conclude with `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ => by ring`.

Establish `h3 : w = 0`. Establish `: Ph⁻¹.mulVec (Ph.mulVec w) = w`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Ph hPh, Matrix.one_mulVec]`. Rewrite using `[← this, h1, Matrix.mulVec_zero]`. Establish `h4 : ∑ b, (g b ^ Fintype.card K) • X b = 0`.

Use function extensionality and compare the values at `l`. Use `congrArg (fun z => z ^ Fintype.card K) (congrFun h3 l)` as an intermediate fact. Simplify using `only [hw, frob_sum, mul_pow, frob_frob h2, Pi.zero_apply] at this`. Rewrite `this` using `[zero_pow Fintype.card_pos.ne']`. Simplify `this` using `[Finset.sum_apply]`.

Introduce `b`. Use `(Fintype.linearIndependent_iff.1 hX) _ h4 b` as an intermediate fact. Conclude with `pow_eq_zero_iff (Fintype.card_pos.ne') |>.1 this`.
-/
lemma hMat_li (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det) {j : ℕ} (X : Fin j → Fin n → L)
    (hX : LinearIndependent L X) : LinearIndependent L (hMat K Ph X).row := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set w : Fin n → L := fun l => ∑ b, g b * X b l ^ Fintype.card K with hw
  have h1 : Ph.mulVec w = 0 := by
    funext k
    have := congrFun hg k
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.row, hMat, Matrix.of_apply, smul_eq_mul,
      Pi.zero_apply, Finset.mul_sum] at this
    simp only [Matrix.mulVec, dotProduct, hw, Finset.mul_sum, Pi.zero_apply]
    rw [Finset.sum_comm, ← this]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ => by ring
  have h3 : w = 0 := by
    have : Ph⁻¹.mulVec (Ph.mulVec w) = w := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Ph hPh, Matrix.one_mulVec]
    rw [← this, h1, Matrix.mulVec_zero]
  have h4 : ∑ b, (g b ^ Fintype.card K) • X b = 0 := by
    funext l
    have := congrArg (fun z => z ^ Fintype.card K) (congrFun h3 l)
    simp only [hw, frob_sum, mul_pow, frob_frob h2, Pi.zero_apply] at this
    rw [zero_pow Fintype.card_pos.ne'] at this
    simpa [Finset.sum_apply] using this
  intro b
  have := (Fintype.linearIndependent_iff.1 hX) _ h4 b
  exact pow_eq_zero_iff (Fintype.card_pos.ne') |>.1 this

end inert2

section inert3
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)

open scoped Classical in
/- English proof (translation)
Set `ℓ : (Fin n → L) → (Fin j → L)` to `fun x b => hB K Ph x (X b)`. Establish `hℓ : ∀ u d, ℓ (u + d) = ℓ u + ℓ d` using `fun u d => by`. Use function extensionality and compare the values at `b`. Conclude with `hB_add_left Ph u d (X b)`. Establish `hbqadd : ∀ u d, bq (u + d) = bq u + bq d + Algebra.trace K L (hB K Ph u d)`.

Introduce `u d`. Apply `(algebraMap K L).injective` to reduce the goal to its premises. Rewrite using `[map_add, map_add, hbq, hbq, hbq, trace_eq h2, hB_conj Ph h2 hherm, hB_add_left, hB_add_right, hB_add_right]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfil : (univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b)) = univ.filter (fun x : Fin n → L => ℓ x + (-g) = 0)`.

Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, ℓ]`. Rewrite using `[← sub_eq_add_neg, sub_eq_zero, funext_iff]`. Establish `h0` using `orth_sum (fun x : Fin n → L => ℓ x + (-g)) (fun x => ψ (bq x))`. Rewrite `h0` using `[← hfil]`.

Establish `hχ : ∀ χ : AddChar (Fin j → L) ℂ, ‖∑ x, χ (ℓ x + (-g)) * ψ (bq x)‖ ≤ (Fintype.card K : ℝ) ^ n`. Introduce `χ`. Establish `e1 : ∑ x, χ (ℓ x + (-g)) * ψ (bq x) = χ (-g) * ∑ x, χ (ℓ x) * ψ (bq x)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[AddChar.map_add_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, norm_mul, AddChar.norm_apply, one_mul]`. Use `gauss_inert h2 n Ph hPh ψ hψ (fun x => χ (ℓ x) * ψ (bq x)) (fun u => ?_) (fun u d => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, AddChar.norm_apply, AddChar.norm_apply, one_mul]`.

Express the relevant statement in the definitionally equal form `χ (ℓ (u + d)) * ψ (bq (u + d)) = χ (ℓ u) * ψ (bq u) * (χ (ℓ d) * ψ (bq d)) * ψ (Algebra.trace K L (hB K Ph u d))`. Rewrite using `[hℓ, hbqadd, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hT : (0 : ℝ) < (Fintype.card (Fin j → L) : ℝ)`. Conclude with `Fintype.card_pos` after adjusting the coercions.

Establish `h1 : ‖∑ x ∈ univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b), ψ (bq x)‖ * (Fintype.card (Fin j → L) : ℝ) ≤ (Fintype.card K : ℝ) ^ n * (Fintype.card (Fin j → L) : ℝ)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h0]`. Conclude with `norm_sum_le _ _`. Use `_ ≤ ∑ χ : AddChar (Fin j → L) ℂ, (Fintype.card K : ℝ) ^ n := Finset.sum_le_sum fun χ _ => hχ χ`.

Use `_ = _ := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, AddChar.card_eq, nsmul_eq_mul, mul_comm]`. Conclude with `le_of_mul_le_mul_right h1 hT`.
-/
lemma sumA_bound (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det)
    (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K) {j : ℕ} (X : Fin j → Fin n → L)
    (g : Fin j → L) (bq : (Fin n → L) → K) (hbq : ∀ x, algebraMap K L (bq x) = hB K Ph x x)
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 0) :
    ‖∑ x ∈ univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b), ψ (bq x)‖
      ≤ (Fintype.card K : ℝ) ^ n := by
  let ℓ : (Fin n → L) → (Fin j → L) := fun x b => hB K Ph x (X b)
  have hℓ : ∀ u d, ℓ (u + d) = ℓ u + ℓ d := fun u d => by
    funext b; exact hB_add_left Ph u d (X b)
  have hbqadd : ∀ u d, bq (u + d) = bq u + bq d + Algebra.trace K L (hB K Ph u d) := by
    intro u d
    apply (algebraMap K L).injective
    rw [map_add, map_add, hbq, hbq, hbq, trace_eq h2, hB_conj Ph h2 hherm, hB_add_left,
      hB_add_right, hB_add_right]
    ring
  have hfil : (univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b))
      = univ.filter (fun x : Fin n → L => ℓ x + (-g) = 0) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ℓ]
    rw [← sub_eq_add_neg, sub_eq_zero, funext_iff]
  have h0 := orth_sum (fun x : Fin n → L => ℓ x + (-g)) (fun x => ψ (bq x))
  rw [← hfil] at h0
  have hχ : ∀ χ : AddChar (Fin j → L) ℂ, ‖∑ x, χ (ℓ x + (-g)) * ψ (bq x)‖ ≤ (Fintype.card K : ℝ) ^ n := by
    intro χ
    have e1 : ∑ x, χ (ℓ x + (-g)) * ψ (bq x) = χ (-g) * ∑ x, χ (ℓ x) * ψ (bq x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [AddChar.map_add_eq_mul]; ring
    rw [e1, norm_mul, AddChar.norm_apply, one_mul]
    refine gauss_inert h2 n Ph hPh ψ hψ (fun x => χ (ℓ x) * ψ (bq x)) (fun u => ?_) (fun u d => ?_)
    · rw [norm_mul, AddChar.norm_apply, AddChar.norm_apply, one_mul]
    · change χ (ℓ (u + d)) * ψ (bq (u + d)) = χ (ℓ u) * ψ (bq u) * (χ (ℓ d) * ψ (bq d)) *
        ψ (Algebra.trace K L (hB K Ph u d))
      rw [hℓ, hbqadd, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
      ring
  have hT : (0 : ℝ) < (Fintype.card (Fin j → L) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have h1 : ‖∑ x ∈ univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b), ψ (bq x)‖
      * (Fintype.card (Fin j → L) : ℝ) ≤ (Fintype.card K : ℝ) ^ n * (Fintype.card (Fin j → L) : ℝ) := by
    calc _ = ‖(∑ x ∈ univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b), ψ (bq x))
          * (Fintype.card (Fin j → L) : ℂ)‖ := by rw [norm_mul]; simp
      _ ≤ ∑ χ : AddChar (Fin j → L) ℂ, ‖∑ x, χ (ℓ x + (-g)) * ψ (bq x)‖ := by
          rw [h0]; exact norm_sum_le _ _
      _ ≤ ∑ χ : AddChar (Fin j → L) ℂ, (Fintype.card K : ℝ) ^ n := Finset.sum_le_sum fun χ _ => hχ χ
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, AddChar.card_eq, nsmul_eq_mul, mul_comm]
  exact le_of_mul_le_mul_right h1 hT

open scoped Classical in
/- English proof (translation)
The claim follows from `|(Fintype.card K : ℝ) * ((univ.filter (fun x : Fin n → L => (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ) - c| ≤ (Fintype.card K : ℝ) * (Fintype.card K : ℝ) ^ n := by obtain ⟨θ, hθ⟩ := trace_surj (K := K) (L := L) 1 have hθ' : θ + θ ^ Fintype.card K = 1 := by rw [← t …`.
-/
lemma step_Z (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det)
    (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K) {j : ℕ} (X : Fin j → Fin n → L)
    (hX : LinearIndependent L X) (g : Fin j → L) (a : L) (ha : a ^ Fintype.card K = a) (c : ℕ)
    (hc : c * (Fintype.card K ^ 2) ^ j = (Fintype.card K ^ 2) ^ n) :
    |(Fintype.card K : ℝ) * ((univ.filter (fun x : Fin n → L =>
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ) - c|
      ≤ (Fintype.card K : ℝ) * (Fintype.card K : ℝ) ^ n := by
  obtain ⟨θ, hθ⟩ := trace_surj (K := K) (L := L) 1
  have hθ' : θ + θ ^ Fintype.card K = 1 := by
    rw [← trace_eq h2, hθ, map_one]
  have hfix : ∀ z : L, z ^ Fintype.card K = z → algebraMap K L (Algebra.trace K L (θ * z)) = z := by
    intro z hz
    rw [trace_eq h2, mul_pow, hz]
    linear_combination z * hθ'
  let bq : (Fin n → L) → K := fun x => Algebra.trace K L (θ * hB K Ph x x)
  have hbq : ∀ x, algebraMap K L (bq x) = hB K Ph x x := fun x => hfix _ (hB_conj Ph h2 hherm x x)
  let a0 : K := Algebra.trace K L (θ * a)
  have ha0 : algebraMap K L a0 = a := hfix a ha
  have hQ : ∀ x, bq x + (-a0) = 0 ↔ hB K Ph x x = a := by
    intro x
    rw [← sub_eq_add_neg, sub_eq_zero, ← hbq, ← ha0]
    exact (algebraMap K L).injective.eq_iff.symm
  have hA : (univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b)).card = c := by
    have h1 := fiber_card (hMat K Ph X) (hMat_li Ph h2 hPh X hX) g
    rw [card_L h2, ← hc] at h1
    have h3 := Nat.eq_of_mul_eq_mul_right (by positivity) h1
    rw [← h3]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hB_mulVec, funext_iff]
  have h0 := orth_sum (fun x : Fin n → L => bq x + (-a0))
    (fun x => if (∀ b, hB K Ph x (X b) = g b) then (1 : ℂ) else 0)
  have hL : ∑ x ∈ univ.filter (fun x : Fin n → L => bq x + (-a0) = 0),
      (if (∀ b, hB K Ph x (X b) = g b) then (1 : ℂ) else 0)
      = ((univ.filter (fun x : Fin n → L => (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℂ) := by
    rw [Finset.sum_boole, Finset.filter_filter]
    congr 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hQ]
    exact and_comm
  rw [hL, ← Finset.add_sum_erase univ _ (Finset.mem_univ (0 : AddChar K ℂ))] at h0
  simp only [AddChar.zero_apply, one_mul] at h0
  rw [Finset.sum_boole, hA] at h0
  have hψb : ∀ ψ ∈ univ.erase (0 : AddChar K ℂ),
      ‖∑ x, ψ (bq x + (-a0)) * (if (∀ b, hB K Ph x (X b) = g b) then (1 : ℂ) else 0)‖
        ≤ (Fintype.card K : ℝ) ^ n := by
    intro ψ hψ
    have e1 : ∑ x, ψ (bq x + (-a0)) * (if (∀ b, hB K Ph x (X b) = g b) then (1 : ℂ) else 0)
        = ψ (-a0) * ∑ x ∈ univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b), ψ (bq x) := by
      rw [Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [AddChar.map_add_eq_mul]
      split_ifs <;> ring
    rw [e1, norm_mul, AddChar.norm_apply, one_mul]
    exact sumA_bound Ph h2 hPh hherm X g bq hbq ψ (Finset.ne_of_mem_erase hψ)
  have e2 : (((Fintype.card K : ℝ) * ((univ.filter (fun x : Fin n → L =>
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ) - c : ℝ) : ℂ)
      = ∑ ψ ∈ univ.erase (0 : AddChar K ℂ),
        ∑ x, ψ (bq x + (-a0)) * (if (∀ b, hB K Ph x (X b) = g b) then (1 : ℂ) else 0) := by
    push_cast
    linear_combination h0
  rw [← Real.norm_eq_abs, ← Complex.norm_real, e2]
  calc _ ≤ ∑ ψ ∈ univ.erase (0 : AddChar K ℂ), _ := norm_sum_le _ _
    _ ≤ ∑ ψ ∈ univ.erase (0 : AddChar K ℂ), (Fintype.card K : ℝ) ^ n := Finset.sum_le_sum hψb
    _ = ((univ.erase (0 : AddChar K ℂ)).card : ℝ) * (Fintype.card K : ℝ) ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        gcongr
        have : (univ.erase (0 : AddChar K ℂ)).card ≤ Fintype.card K := by
          calc _ ≤ (univ : Finset (AddChar K ℂ)).card := Finset.card_le_card (Finset.erase_subset _ _)
            _ = _ := by rw [Finset.card_univ, AddChar.card_eq]
        exact_mod_cast this

open scoped Classical in
/- English proof (translation)
Establish `hZ` using `abs_le.1 (step_Z Ph h2 hPh hherm X hX g a ha c hc)`. Use `set Z := univ.filter (fun x : Fin n → L => (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a) with hZd`. Establish `hsplit` using `Finset.card_filter_add_card_filter_not (s := Z) (fun x => x ∈ Submodule.span L (Set.range X))`. Establish `hs : Z.filter (fun x => ¬ x ∈ Submodule.span L (Set.range X)) = univ.filter (fun x : Fin n → L => x ∉ Submodule.span L (Set.range X) ∧ (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)`. Use extensionality with `x`.

Simplify using `only [hZd, Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `and_comm`. Rewrite `hsplit` using `[hs]`. Establish `hspan : (Z.filter (fun x => x ∈ Submodule.span L (Set.range X))).card ≤ (Fintype.card K ^ 2) ^ j`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.card_le_card fun x hx => ?_` and prove the remaining obligations. Take `⟨cf, hcf⟩` from `(Submodule.mem_span_range_iff_exists_fun L).1 (Finset.mem_filter.1 hx).2`. Conclude with `Finset.mem_image.2 ⟨cf, Finset.mem_univ _, hcf⟩`. Use `_ ≤ (univ : Finset (Fin j → L)).card := Finset.card_image_le`. Use `_ = _ := by simp [card_L h2]`.

Establish `hspanR : ((Z.filter (fun x => x ∈ Submodule.span L (Set.range X))).card : ℝ) ≤ ((Fintype.card K : ℝ) ^ 2) ^ j` using `by exact_mod_cast hspan`. Establish `hsplitR : ((Z.filter (fun x => x ∈ Submodule.span L (Set.range X))).card : ℝ) + ((univ.filter (fun x : Fin n → L => x ∉ Submodule.span L (Set.range X) ∧ (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ) = (Z.card : ℝ)`. Conclude with `hsplit` after adjusting the coercions. Establish `hq0 : (0 : ℝ) ≤ (Fintype.card K : ℝ)` using `Nat.cast_nonneg _`. Establish `h0 : (0 : ℝ) ≤ ((Z.filter (fun x => x ∈ Submodule.span L (Set.range X))).card : ℝ)` using `Nat.cast_nonneg _`.

Prove the components needed by the constructor for the conclusion. Use polynomial arithmetic with `[hZ.2]`. Use polynomial arithmetic with `[hZ.1]`.
-/
lemma step_alt (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det)
    (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K) {j : ℕ} (X : Fin j → Fin n → L)
    (hX : LinearIndependent L X) (g : Fin j → L) (a : L) (ha : a ^ Fintype.card K = a) (c : ℕ)
    (hc : c * (Fintype.card K ^ 2) ^ j = (Fintype.card K ^ 2) ^ n) :
    (Fintype.card K : ℝ) * ((univ.filter (fun x : Fin n → L => x ∉ Submodule.span L (Set.range X) ∧
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ)
      ≤ c + (Fintype.card K : ℝ) * (Fintype.card K : ℝ) ^ n ∧
    (c : ℝ) - (Fintype.card K : ℝ) * (Fintype.card K : ℝ) ^ n
        - (Fintype.card K : ℝ) * ((Fintype.card K : ℝ) ^ 2) ^ j
      ≤ (Fintype.card K : ℝ) * ((univ.filter (fun x : Fin n → L => x ∉ Submodule.span L (Set.range X) ∧
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ) := by
  have hZ := abs_le.1 (step_Z Ph h2 hPh hherm X hX g a ha c hc)
  set Z := univ.filter (fun x : Fin n → L => (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a) with hZd
  have hsplit := Finset.card_filter_add_card_filter_not (s := Z)
    (fun x => x ∈ Submodule.span L (Set.range X))
  have hs : Z.filter (fun x => ¬ x ∈ Submodule.span L (Set.range X))
      = univ.filter (fun x : Fin n → L => x ∉ Submodule.span L (Set.range X) ∧
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a) := by
    ext x
    simp only [hZd, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hs] at hsplit
  have hspan : (Z.filter (fun x => x ∈ Submodule.span L (Set.range X))).card
      ≤ (Fintype.card K ^ 2) ^ j := by
    calc _ ≤ (univ.image fun cf : Fin j → L => ∑ b, cf b • X b).card := by
          refine Finset.card_le_card fun x hx => ?_
          obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 (Finset.mem_filter.1 hx).2
          exact Finset.mem_image.2 ⟨cf, Finset.mem_univ _, hcf⟩
      _ ≤ (univ : Finset (Fin j → L)).card := Finset.card_image_le
      _ = _ := by simp [card_L h2]
  have hspanR : ((Z.filter (fun x => x ∈ Submodule.span L (Set.range X))).card : ℝ)
      ≤ ((Fintype.card K : ℝ) ^ 2) ^ j := by exact_mod_cast hspan
  have hsplitR : ((Z.filter (fun x => x ∈ Submodule.span L (Set.range X))).card : ℝ)
      + ((univ.filter (fun x : Fin n → L => x ∉ Submodule.span L (Set.range X) ∧
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ) = (Z.card : ℝ) := by
    exact_mod_cast hsplit
  have hq0 : (0 : ℝ) ≤ (Fintype.card K : ℝ) := Nat.cast_nonneg _
  have h0 : (0 : ℝ) ≤ ((Z.filter (fun x => x ∈ Submodule.span L (Set.range X))).card : ℝ) :=
    Nat.cast_nonneg _
  constructor
  · nlinarith [hZ.2]
  · nlinarith [hZ.1]

end inert3

/- English proof (translation)
Take `⟨d, hd⟩ : ∃ d, d = a / N` from `⟨_, rfl⟩`. Establish `hq0 : 0 < q` using `by linarith`. Establish `hd0 : 0 < d` using `by rw [hd]; positivity`. Establish `haN : a = N * d` using `by rw [hd]; field_simp`. Establish `hW0 : 0 < W`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `: W * a ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg h ha.le`. Establish `: 0 < N ^ 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hNW : N = W * d`. Establish `: W * d * N = N * N` using `by rw [mul_assoc, mul_comm d N, ← haN, hWa]; ring`. Conclude with `(mul_right_cancel₀ hN.ne' this).symm`. Establish `hqd : q ^ 2 * d ≤ 1 / 8`. Establish `: q ^ 2 * (N * d) * 8 ≤ N` using `by rw [← haN]; exact hsmall`.

Establish `h3 : N * (q ^ 2 * d * 8) ≤ N * 1` using `by nlinarith`. Use `le_of_mul_le_mul_left h3 hN` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hqd1 : q * d ≤ 1 / 8` using `by nlinarith`. Establish `hd1 : d ≤ 1 / 8` using `by nlinarith`.

Establish `e1 : q ^ 2 * a / N = q ^ 2 * d` using `by rw [hd]; ring`. Rewrite using `[e1]`. Rewrite `h1`, `h2` using `[← hd]`. Establish `hlo' : lo = (1 - q * d - q * d ^ 2) * (W / q)`. Rewrite using `[hlo, haN, hNW]`.

Clear the denominators using the available nonvanishing facts. Establish `hhi' : hi = (1 + q * d) * (W / q)`. Rewrite using `[hhi, hNW]`. Clear the denominators using the available nonvanishing facts. Establish `hWq : 0 < W / q` using `by positivity`.

Establish `hCj0 : 0 ≤ Cj` using `le_trans (mul_nonneg (by linarith) hQ) h1`. Establish `hA : 0 ≤ q ^ 2 - q - 2` using `by nlinarith`. Establish `key1 : (1 + d) * (1 + q * d) ≤ 1 + q ^ 2 * d`. Use polynomial arithmetic with `[mul_nonneg hd0.le hA, mul_nonneg hd0.le (sub_nonneg.2 hqd1)]`. Establish `key2 : 1 - q ^ 2 * d ≤ (1 - d) * (1 - q * d - q * d ^ 2)`.

Use polynomial arithmetic with `[mul_nonneg hd0.le hA, mul_pos hq0 (pow_pos hd0 3)]`. Establish `hl0 : 0 ≤ 1 - q * d - q * d ^ 2` using `by nlinarith`. Establish `hP : 0 ≤ Qj * (W / q)` using `mul_nonneg hQ hWq.le`. Establish `eP : Qj * W / q = Qj * (W / q)` using `by ring`. Rewrite using `[eP]`.

Prove the components needed by the constructor for the conclusion. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right h1` to reduce the goal to its premises. Rewrite using `[hlo']`. Check the signs of the components of the expression.

Use `_ ≤ C' := hC1`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right h2` to reduce the goal to its premises. Rewrite using `[hhi']`. Check the signs of the components of the expression.

Use `_ = ((1 + d) * (1 + q * d)) * (Qj * (W / q)) := by rw [hhi']; ring`. Use `_ ≤ _ := mul_le_mul_of_nonneg_right key1 hP`.
-/
lemma step_arith (q N a W Qj Cj C' lo hi : ℝ) (hq : 2 ≤ q) (hN : 0 < N) (ha : 0 < a)
    (hWa : W * a = N ^ 2) (hsmall : q ^ 2 * a * 8 ≤ N) (hQ : 0 ≤ Qj)
    (h1 : (1 - a / N) * Qj ≤ Cj) (h2 : Cj ≤ (1 + a / N) * Qj)
    (hlo : lo = (W - q * N - q * a) / q) (hhi : hi = (W + q * N) / q)
    (hC1 : Cj * lo ≤ C') (hC2 : C' ≤ Cj * hi) :
    (1 - q ^ 2 * a / N) * (Qj * W / q) ≤ C' ∧ C' ≤ (1 + q ^ 2 * a / N) * (Qj * W / q) := by
  obtain ⟨d, hd⟩ : ∃ d, d = a / N := ⟨_, rfl⟩
  have hq0 : 0 < q := by linarith
  have hd0 : 0 < d := by rw [hd]; positivity
  have haN : a = N * d := by rw [hd]; field_simp
  have hW0 : 0 < W := by
    by_contra h
    push Not at h
    have : W * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h ha.le
    have : 0 < N ^ 2 := by positivity
    linarith
  have hNW : N = W * d := by
    have : W * d * N = N * N := by rw [mul_assoc, mul_comm d N, ← haN, hWa]; ring
    exact (mul_right_cancel₀ hN.ne' this).symm
  have hqd : q ^ 2 * d ≤ 1 / 8 := by
    have : q ^ 2 * (N * d) * 8 ≤ N := by rw [← haN]; exact hsmall
    have h3 : N * (q ^ 2 * d * 8) ≤ N * 1 := by nlinarith
    have := le_of_mul_le_mul_left h3 hN
    linarith
  have hqd1 : q * d ≤ 1 / 8 := by nlinarith
  have hd1 : d ≤ 1 / 8 := by nlinarith
  have e1 : q ^ 2 * a / N = q ^ 2 * d := by rw [hd]; ring
  rw [e1]
  rw [← hd] at h1 h2
  have hlo' : lo = (1 - q * d - q * d ^ 2) * (W / q) := by
    rw [hlo, haN, hNW]; field_simp
  have hhi' : hi = (1 + q * d) * (W / q) := by
    rw [hhi, hNW]; field_simp
  have hWq : 0 < W / q := by positivity
  have hCj0 : 0 ≤ Cj := le_trans (mul_nonneg (by linarith) hQ) h1
  have hA : 0 ≤ q ^ 2 - q - 2 := by nlinarith
  have key1 : (1 + d) * (1 + q * d) ≤ 1 + q ^ 2 * d := by
    nlinarith [mul_nonneg hd0.le hA, mul_nonneg hd0.le (sub_nonneg.2 hqd1)]
  have key2 : 1 - q ^ 2 * d ≤ (1 - d) * (1 - q * d - q * d ^ 2) := by
    nlinarith [mul_nonneg hd0.le hA, mul_pos hq0 (pow_pos hd0 3)]
  have hl0 : 0 ≤ 1 - q * d - q * d ^ 2 := by nlinarith
  have hP : 0 ≤ Qj * (W / q) := mul_nonneg hQ hWq.le
  have eP : Qj * W / q = Qj * (W / q) := by ring
  rw [eP]
  constructor
  · calc (1 - q ^ 2 * d) * (Qj * (W / q)) ≤ ((1 - d) * (1 - q * d - q * d ^ 2)) * (Qj * (W / q)) :=
          mul_le_mul_of_nonneg_right key2 hP
      _ = ((1 - d) * Qj) * lo := by rw [hlo']; ring
      _ ≤ Cj * lo := by
          apply mul_le_mul_of_nonneg_right h1
          rw [hlo']; positivity
      _ ≤ C' := hC1
  · calc C' ≤ Cj * hi := hC2
      _ ≤ ((1 + d) * Qj) * hi := by
          apply mul_le_mul_of_nonneg_right h2
          rw [hhi']; positivity
      _ = ((1 + d) * (1 + q * d)) * (Qj * (W / q)) := by rw [hhi']; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right key1 hP

section inert4
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)

open scoped Classical in
/- English proof (translation)
Establish `key : ∀ (x : Fin n → L) (X' : Fin j → Fin n → L), (LinearIndependent L (Fin.cons x X' : Fin (j + 1) → Fin n → L) ∧ ∀ a b, hB K Ph ((Fin.cons x X' : Fin (j + 1) → Fin n → L) a) ((Fin.cons x X' : Fin (j + 1) → Fin n → L) b) = G a b) ↔ ((LinearIndependent L X' ∧ ∀ a b, hB K Ph (X' a …`. Introduce `x X'`. Rewrite using `[linearIndependent_finCons]`. Simplify using `only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨h1, h3⟩, ⟨h4, h5⟩, h6⟩`. Conclude with `⟨⟨h1, fun a b => (h6 a).2 b⟩, h3, h5, h4⟩`. Introduce and unpack `⟨⟨h1, h3⟩, h4, h5, h6⟩`. Use `⟨⟨h1, h4⟩, ⟨h6, h5⟩, fun a => ⟨?_, h3 a⟩⟩` and prove the remaining obligations. Rewrite using `[← hB_conj Ph h2 hherm, h5, ← hG]`.

Rewrite using `[Finset.card_filter, ← (Fin.consEquiv (fun _ => Fin n → L)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun X' _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.card_filter]`. Distinguish the cases in `hV : LinearIndependent L X' ∧ ∀ a b, hB K Ph (X' a) (X' b) = G a.succ b.succ`. Rewrite using `[if_pos hV]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Conclude with `if_congr ((key x X').trans (and_iff_right hV)) rfl rfl`. Rewrite using `[if_neg hV]`. Use `Finset.sum_eq_zero fun x _ => ?_` and prove the remaining obligations. Conclude with `if_neg fun h => hV ((key x X').1 h).1`.
-/
lemma cnt_succ (h2 : Module.finrank K L = 2) (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K)
    (j : ℕ) (G : Matrix (Fin (j + 1)) (Fin (j + 1)) L) (hG : ∀ a b, G b a = G a b ^ Fintype.card K) :
    (univ.filter fun X : Fin (j + 1) → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = G a b).card
      = ∑ X' ∈ univ.filter (fun X' : Fin j → Fin n → L => LinearIndependent L X' ∧
          ∀ a b, hB K Ph (X' a) (X' b) = G a.succ b.succ),
        (univ.filter fun x : Fin n → L => x ∉ Submodule.span L (Set.range X') ∧
          (∀ b, hB K Ph x (X' b) = G 0 b.succ) ∧ hB K Ph x x = G 0 0).card := by
  have key : ∀ (x : Fin n → L) (X' : Fin j → Fin n → L),
      (LinearIndependent L (Fin.cons x X' : Fin (j + 1) → Fin n → L) ∧
        ∀ a b, hB K Ph ((Fin.cons x X' : Fin (j + 1) → Fin n → L) a)
          ((Fin.cons x X' : Fin (j + 1) → Fin n → L) b) = G a b) ↔
      ((LinearIndependent L X' ∧ ∀ a b, hB K Ph (X' a) (X' b) = G a.succ b.succ) ∧
        (x ∉ Submodule.span L (Set.range X') ∧
          (∀ b, hB K Ph x (X' b) = G 0 b.succ) ∧ hB K Ph x x = G 0 0)) := by
    intro x X'
    rw [linearIndependent_finCons]
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    constructor
    · rintro ⟨⟨h1, h3⟩, ⟨h4, h5⟩, h6⟩
      exact ⟨⟨h1, fun a b => (h6 a).2 b⟩, h3, h5, h4⟩
    · rintro ⟨⟨h1, h3⟩, h4, h5, h6⟩
      refine ⟨⟨h1, h4⟩, ⟨h6, h5⟩, fun a => ⟨?_, h3 a⟩⟩
      rw [← hB_conj Ph h2 hherm, h5, ← hG]
  rw [Finset.card_filter, ← (Fin.consEquiv (fun _ => Fin n → L)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun X' _ => ?_
  rw [Finset.card_filter]
  by_cases hV : LinearIndependent L X' ∧ ∀ a b, hB K Ph (X' a) (X' b) = G a.succ b.succ
  · rw [if_pos hV]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact if_congr ((key x X').trans (and_iff_right hV)) rfl rfl
  · rw [if_neg hV]
    refine Finset.sum_eq_zero fun x _ => ?_
    exact if_neg fun h => hV ((key x X').1 h).1

open scoped Classical in
/- English proof (translation)
Establish `hq2 : (2 : ℝ) ≤ (Fintype.card K : ℝ)` using `by exact_mod_cast Fintype.one_lt_card (α := K)`. Establish `hq0 : (0 : ℝ) < (Fintype.card K : ℝ)` using `by linarith`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_ G _`.

Establish `: (univ.filter fun X : Fin 0 → Fin n → L => LinearIndependent L X ∧ ∀ a b, hB K Ph (X a) (X b) = G a b) = univ`. Use extensionality with `X`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]`. Conclude with `⟨linearIndependent_empty_type, fun a => a.elim0⟩`. Rewrite using `[this]`.

Establish `hd : 0 ≤ 1 / (Fintype.card K : ℝ) ^ n` using `by positivity`. Simplify using `only [Finset.card_univ, Fintype.card_unique, Nat.cast_one, pow_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_one, mul_one]`. Apply the tactic sequence `constructor <;> linarith`. Consider the case `succ j ih`. Introduce `hn G hG`.

Take `⟨t, rfl⟩ : ∃ t, n = j + t` from `⟨n - j, by omega⟩`. Establish `ih'` using `ih (by omega) (G.submatrix Fin.succ Fin.succ) (fun a b => hG _ _)`. Simplify using `only [Matrix.submatrix_apply] at ih'`. Rewrite using `[cnt_succ Ph h2 hherm j G hG]`. Use `set valid := univ.filter (fun X' : Fin j → Fin (j + t) → L => LinearIndependent L X' ∧ ∀ a b, hB K Ph (X' a) (X' b) = G a.succ b.succ) with hvalid`.

Establish `hc : (Fintype.card K ^ 2) ^ t * (Fintype.card K ^ 2) ^ j = (Fintype.card K ^ 2) ^ (j + t)`. Rewrite using `[← pow_add, add_comm]`. Establish `hstep : ∀ X' ∈ valid, _` using `fun X' hX' => step_alt Ph h2 hPh hherm X' (Finset.mem_filter.1 hX').2.1 (fun b => G 0 b.succ) (G 0 0) (hG 0 0).symm ((Fintype.card K ^ 2) ^ t) hc`. Use `push_cast`. Move the coercions through the operations in `at hstep`.

Use `set q : ℝ := (Fintype.card K : ℝ) with hq`. Establish `hres` using `step_arith q (q ^ (j + t)) ((q ^ 2) ^ j) ((q ^ 2) ^ t) (q ^ (2 * (j + t) * j) / q ^ (j ^ 2)) (valid.card : ℝ) (∑ X' ∈ valid, ((univ.filter fun x : Fin (j + t) → L => x ∉ Submodule.span L (Set.range X') ∧ (∀ b, hB K Ph x (X' b) = G 0 b.succ) ∧ hB K Ph x x = G 0 0).card : ℝ)) (((q …`. Establish `h8 : (8 : ℝ) ≤ q ^ 3`. Combine the equalities or inequalities in the displayed calculation. Establish `e : q ^ (j + t) = q ^ 2 * (q ^ 2) ^ j * q ^ (t - j - 2)`.

Rewrite using `[← pow_mul, ← pow_add, ← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `h3 : q ^ 3 ≤ q ^ (t - j - 2)` using `pow_le_pow_right₀ (by linarith) (by omega)`. Rewrite using `[e]`.

Establish `: 0 < q ^ 2 * (q ^ 2) ^ j` using `by positivity`. Use the proof step `nlinarith)`. Use the proof step `(by positivity) ih'.1 ih'.2 rfl rfl`. Use the proof step `(by`. Rewrite using `[← nsmul_eq_mul]`.

Use `Finset.card_nsmul_le_sum _ _ _ fun X' hX' => ?_` and prove the remaining obligations. Rewrite using `[div_le_iff₀ hq0]`. Combine the linear relations using `[(hstep X' hX').2])`. Use the proof step `(by`. Rewrite using `[← nsmul_eq_mul]`.

Use `Finset.sum_le_card_nsmul _ _ _ fun X' hX' => ?_` and prove the remaining obligations. Rewrite using `[le_div_iff₀ hq0]`. Combine the linear relations using `[(hstep X' hX').1])`. Establish `eQ : q ^ (2 * (j + t) * (j + 1)) / q ^ ((j + 1) ^ 2) = q ^ (2 * (j + t) * j) / q ^ (j ^ 2) * (q ^ 2) ^ t / q`. Rewrite using `[div_mul_eq_mul_div, div_div, div_eq_div_iff (by positivity) (by positivity), ← pow_mul, ← pow_succ, ← pow_add, ← pow_add, ← pow_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `ed : (q ^ 2) ^ (j + 1) / q ^ (j + t) = q ^ 2 * (q ^ 2) ^ j / q ^ (j + t)`. Rewrite using `[pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[eQ, ed]`. Conclude with `hres`.
-/
lemma cnt_bounds (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det)
    (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K) (j : ℕ) : 2 * j + 3 ≤ n →
    ∀ G : Matrix (Fin j) (Fin j) L, (∀ a b, G b a = G a b ^ Fintype.card K) →
    (1 - ((Fintype.card K : ℝ) ^ 2) ^ j / (Fintype.card K : ℝ) ^ n) *
        ((Fintype.card K : ℝ) ^ (2 * n * j) / (Fintype.card K : ℝ) ^ (j ^ 2))
      ≤ ((univ.filter fun X : Fin j → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = G a b).card : ℝ) ∧
    ((univ.filter fun X : Fin j → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = G a b).card : ℝ)
      ≤ (1 + ((Fintype.card K : ℝ) ^ 2) ^ j / (Fintype.card K : ℝ) ^ n) *
        ((Fintype.card K : ℝ) ^ (2 * n * j) / (Fintype.card K : ℝ) ^ (j ^ 2)) := by
  have hq2 : (2 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hq0 : (0 : ℝ) < (Fintype.card K : ℝ) := by linarith
  induction j with
  | zero =>
    intro _ G _
    have : (univ.filter fun X : Fin 0 → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = G a b) = univ := by
      ext X
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact ⟨linearIndependent_empty_type, fun a => a.elim0⟩
    rw [this]
    have hd : 0 ≤ 1 / (Fintype.card K : ℝ) ^ n := by positivity
    simp only [Finset.card_univ, Fintype.card_unique, Nat.cast_one, pow_zero, mul_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_one, mul_one]
    constructor <;> linarith
  | succ j ih =>
    intro hn G hG
    obtain ⟨t, rfl⟩ : ∃ t, n = j + t := ⟨n - j, by omega⟩
    have ih' := ih (by omega) (G.submatrix Fin.succ Fin.succ) (fun a b => hG _ _)
    simp only [Matrix.submatrix_apply] at ih'
    rw [cnt_succ Ph h2 hherm j G hG]
    set valid := univ.filter (fun X' : Fin j → Fin (j + t) → L => LinearIndependent L X' ∧
          ∀ a b, hB K Ph (X' a) (X' b) = G a.succ b.succ) with hvalid
    have hc : (Fintype.card K ^ 2) ^ t * (Fintype.card K ^ 2) ^ j = (Fintype.card K ^ 2) ^ (j + t) := by
      rw [← pow_add, add_comm]
    have hstep : ∀ X' ∈ valid, _ := fun X' hX' =>
      step_alt Ph h2 hPh hherm X' (Finset.mem_filter.1 hX').2.1 (fun b => G 0 b.succ) (G 0 0)
        (hG 0 0).symm ((Fintype.card K ^ 2) ^ t) hc
    push_cast
    push_cast at hstep
    set q : ℝ := (Fintype.card K : ℝ) with hq
    have hres := step_arith q (q ^ (j + t)) ((q ^ 2) ^ j) ((q ^ 2) ^ t)
      (q ^ (2 * (j + t) * j) / q ^ (j ^ 2)) (valid.card : ℝ)
      (∑ X' ∈ valid, ((univ.filter fun x : Fin (j + t) → L => x ∉ Submodule.span L (Set.range X') ∧
          (∀ b, hB K Ph x (X' b) = G 0 b.succ) ∧ hB K Ph x x = G 0 0).card : ℝ))
      (((q ^ 2) ^ t - q * q ^ (j + t) - q * (q ^ 2) ^ j) / q) (((q ^ 2) ^ t + q * q ^ (j + t)) / q)
      hq2 (by positivity) (by positivity)
      (by rw [← pow_add, ← pow_mul, ← pow_mul]; congr 1; ring)
      (by
        have h8 : (8 : ℝ) ≤ q ^ 3 := by
          calc (8 : ℝ) = 2 ^ 3 := by norm_num
            _ ≤ q ^ 3 := by gcongr
        have e : q ^ (j + t) = q ^ 2 * (q ^ 2) ^ j * q ^ (t - j - 2) := by
          rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
        have h3 : q ^ 3 ≤ q ^ (t - j - 2) := pow_le_pow_right₀ (by linarith) (by omega)
        rw [e]
        have : 0 < q ^ 2 * (q ^ 2) ^ j := by positivity
        nlinarith)
      (by positivity) ih'.1 ih'.2 rfl rfl
      (by
        rw [← nsmul_eq_mul]
        refine Finset.card_nsmul_le_sum _ _ _ fun X' hX' => ?_
        rw [div_le_iff₀ hq0]
        linarith [(hstep X' hX').2])
      (by
        rw [← nsmul_eq_mul]
        refine Finset.sum_le_card_nsmul _ _ _ fun X' hX' => ?_
        rw [le_div_iff₀ hq0]
        linarith [(hstep X' hX').1])
    have eQ : q ^ (2 * (j + t) * (j + 1)) / q ^ ((j + 1) ^ 2)
        = q ^ (2 * (j + t) * j) / q ^ (j ^ 2) * (q ^ 2) ^ t / q := by
      rw [div_mul_eq_mul_div, div_div, div_eq_div_iff (by positivity) (by positivity), ← pow_mul,
        ← pow_succ, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      ring
    have ed : (q ^ 2) ^ (j + 1) / q ^ (j + t) = q ^ 2 * (q ^ 2) ^ j / q ^ (j + t) := by
      rw [pow_succ]; ring
    rw [eQ, ed]
    exact hres

end inert4

/- English proof (translation)
Introduce `K L _ _ _ _ _ h2 n m Ph Gm hn hPh hherm hG`. Establish `hq2 : (2 : ℝ) ≤ (Fintype.card K : ℝ)` using `by exact_mod_cast Fintype.one_lt_card (α := K)`. Establish `hb` using `cnt_bounds Ph h2 hPh hherm m hn Gm hG`. Establish `hset : {X : Fin m → Fin n → L | LinearIndependent L X ∧ ∀ i j, ∑ k, ∑ l, X i k * Ph k l * X j l ^ Fintype.card K = Gm i j} = ↑(univ.filter fun X : Fin m → Fin n → L => LinearIndependent L X ∧ ∀ a b, hB K Ph (X a) (X b) = Gm a b)`. Use extensionality with `X`.

Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and]`. Both sides reduce to the same expression. Rewrite using `[hset, Set.ncard_coe_finset]`. Use `set q : ℝ := (Fintype.card K : ℝ) with hq`. Establish `hq0 : 0 < q` using `by linarith`.

Establish `hd : (q ^ 2) ^ m / q ^ n ≤ 1 / 8`. Rewrite using `[div_le_iff₀ (by positivity)]`. Establish `h8 : (8 : ℝ) ≤ q ^ 3`. Combine the equalities or inequalities in the displayed calculation. Establish `e : q ^ n = (q ^ 2) ^ m * q ^ (n - 2 * m)`.

Rewrite using `[← pow_mul, ← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `h3 : q ^ 3 ≤ q ^ (n - 2 * m)` using `pow_le_pow_right₀ (by linarith) (by omega)`. Rewrite using `[e]`.

Establish `: 0 < (q ^ 2) ^ m` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hd0 : 0 ≤ (q ^ 2) ^ m / q ^ n` using `by positivity`. Establish `hQ : 0 ≤ q ^ (2 * n * m) / q ^ (m ^ 2)` using `by positivity`. Prove the components needed by the constructor for the conclusion.

Use `le_trans ?_ hb.1` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities. Use `le_trans hb.2 ?_` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem primitive_density_inert_form : PrimDensityInertForm := by
  intro K L _ _ _ _ _ h2 n m Ph Gm hn hPh hherm hG
  classical
  have hq2 : (2 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hb := cnt_bounds Ph h2 hPh hherm m hn Gm hG
  have hset : {X : Fin m → Fin n → L | LinearIndependent L X ∧
      ∀ i j, ∑ k, ∑ l, X i k * Ph k l * X j l ^ Fintype.card K = Gm i j}
      = ↑(univ.filter fun X : Fin m → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = Gm a b) := by
    ext X
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    rfl
  rw [hset, Set.ncard_coe_finset]
  set q : ℝ := (Fintype.card K : ℝ) with hq
  have hq0 : 0 < q := by linarith
  have hd : (q ^ 2) ^ m / q ^ n ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    have h8 : (8 : ℝ) ≤ q ^ 3 := by
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ q ^ 3 := by gcongr
    have e : q ^ n = (q ^ 2) ^ m * q ^ (n - 2 * m) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    have h3 : q ^ 3 ≤ q ^ (n - 2 * m) := pow_le_pow_right₀ (by linarith) (by omega)
    rw [e]
    have : 0 < (q ^ 2) ^ m := by positivity
    nlinarith
  have hd0 : 0 ≤ (q ^ 2) ^ m / q ^ n := by positivity
  have hQ : 0 ≤ q ^ (2 * n * m) / q ^ (m ^ 2) := by positivity
  constructor
  · refine le_trans ?_ hb.1
    nlinarith
  · refine le_trans hb.2 ?_
    nlinarith

/- English proof (translation)
Introduce `K L _ _ _ _ _ h2 n m Gm hn hG`. Use `primitive_density_inert_form K L h2 n m 1 Gm hn (by simp) (fun k l => by` as an intermediate fact. Distinguish the cases in `h : k = l`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Ne.symm h, Fintype.card_pos.ne']) hG`. Simplify `this` using `[Matrix.one_apply, mul_ite, ite_mul, Finset.sum_ite_eq]`.
-/
theorem primitive_density_inert : PrimDensityInert := by
  intro K L _ _ _ _ _ h2 n m Gm hn hG
  have := primitive_density_inert_form K L h2 n m 1 Gm hn (by simp)
    (fun k l => by
      by_cases h : k = l
      · subst h; simp
      · simp [h, Ne.symm h, Fintype.card_pos.ne']) hG
  simpa [Matrix.one_apply, mul_ite, ite_mul, Finset.sum_ite_eq] using this

/- English proof (translation)
Take `⟨e⟩ : Nonempty (κ ↪ ι)` from `Function.Embedding.nonempty_of_card_le hlt.le`. Choose the witnesses or unpack the hypotheses as in `⟨l0, hl0⟩ : ∃ l0, l0 ∉ Set.range e := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `: Function.Surjective e` using `hcon`.

Use `Fintype.card_le_of_surjective e this` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Set `P : Matrix κ ι R` to `(1 : Matrix ι ι R).submatrix e id`. Establish `hPP : P * P.transpose = 1`. Use extensionality with `j j'`.

Simplify using `only [P, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, id, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, e.injective.eq_iff]`. Establish `h1 : A * B = (A * P) * (P.transpose * B)`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP, Matrix.one_mul]`. Rewrite using `[h1, Matrix.det_mul]`. Establish `h2 : (A * P).det = 0`.

Apply `Matrix.det_eq_zero_of_column_eq_zero l0` to reduce the goal to its premises. Introduce `i`. Simplify using `only [P, Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg (fun h => hl0 ⟨j, h⟩), mul_zero]`.

Rewrite using `[h2, zero_mul]`.
-/
lemma det_mul_eq_zero_of_card_lt {R ι κ : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (hlt : Fintype.card κ < Fintype.card ι) (A : Matrix ι κ R) (B : Matrix κ ι R) :
    (A * B).det = 0 := by
  obtain ⟨e⟩ : Nonempty (κ ↪ ι) := Function.Embedding.nonempty_of_card_le hlt.le
  obtain ⟨l0, hl0⟩ : ∃ l0, l0 ∉ Set.range e := by
    by_contra hcon
    push Not at hcon
    have : Function.Surjective e := hcon
    have := Fintype.card_le_of_surjective e this
    omega
  let P : Matrix κ ι R := (1 : Matrix ι ι R).submatrix e id
  have hPP : P * P.transpose = 1 := by
    ext j j'
    simp only [P, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, id,
      Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      e.injective.eq_iff]
  have h1 : A * B = (A * P) * (P.transpose * B) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP, Matrix.one_mul]
  rw [h1, Matrix.det_mul]
  have h2 : (A * P).det = 0 := by
    apply Matrix.det_eq_zero_of_column_eq_zero l0
    intro i
    simp only [P, Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (fun h => hl0 ⟨j, h⟩), mul_zero]
  rw [h2, zero_mul]

section unram2
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]

/- English proof (translation)
Take `⟨l, hl⟩` from `unram_one hU`. Introduce `t t' h`. Establish `e : ∀ t : o, l (algebraMap o O t) = t` using `fun t => by`. Rewrite using `[Algebra.algebraMap_eq_smul_one, map_smul, hl, smul_eq_mul, mul_one]`. Rewrite using `[← e t, ← e t', h]`.
-/
lemma unram_inj (hU : Unram o O) : Function.Injective (algebraMap o O) := by
  obtain ⟨l, hl⟩ := unram_one hU
  intro t t' h
  have e : ∀ t : o, l (algebraMap o O t) = t := fun t => by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hl, smul_eq_mul, mul_one]
  rw [← e t, ← e t', h]

/- English proof (translation)
Take `⟨T, hT⟩` from `unram_trace hU`. Take `⟨s, hs⟩` from `hU.tr_onto 1`. Use `⟨T (y * s), ?_⟩` and prove the remaining obligations. Rewrite using `[hT, star_mul', hy, ← mul_add, hs, map_one, mul_one]`.
-/
lemma unram_fixed (hU : Unram o O) (y : O) (hy : star y = y) : ∃ t : o, algebraMap o O t = y := by
  obtain ⟨T, hT⟩ := unram_trace hU
  obtain ⟨s, hs⟩ := hU.tr_onto 1
  refine ⟨T (y * s), ?_⟩
  rw [hT, star_mul', hy, ← mul_add, hs, map_one, mul_one]

def mO (o O : Type) [CommRing o] [IsLocalRing o] [CommRing O] [Algebra o O] : Ideal O :=
  (IsLocalRing.maximalIdeal o).map (algebraMap o O)

/- English proof (translation)
Take `⟨l, hl⟩` from `unram_one hU`. Set `J' : Ideal O` to `{ carrier := {x | ∀ y, l (y * x) ∈ IsLocalRing.maximalIdeal o} add_mem' := fun {a b} ha hb y => by`. Rewrite using `[mul_add, map_add]`. Conclude with `Ideal.add_mem _ (ha y) (hb y)`. Use the proof step `zero_mem' := fun y => by rw [mul_zero, map_zero]; exact Ideal.zero_mem _`.

Use the proof step `smul_mem' := fun c x hx y => by`. Rewrite using `[smul_eq_mul, ← mul_assoc]`. Conclude with `hx (y * c) }`. Establish `hle : mO o O ≤ J'`. Rewrite using `[mO, Ideal.map_le_iff_le_comap]`.

Introduce `t ht y`. Rewrite using `[mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ ht`. Introduce `h1`. Use `hle h1 1` as an intermediate fact.

Rewrite `this` using `[mul_one, hl]`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal o).ne_top ((Ideal.eq_top_iff_one _).2 this)`.
-/
lemma mO_ne_top (hU : Unram o O) : (1 : O) ∉ mO o O := by
  obtain ⟨l, hl⟩ := unram_one hU
  let J' : Ideal O :=
    { carrier := {x | ∀ y, l (y * x) ∈ IsLocalRing.maximalIdeal o}
      add_mem' := fun {a b} ha hb y => by
        rw [mul_add, map_add]; exact Ideal.add_mem _ (ha y) (hb y)
      zero_mem' := fun y => by rw [mul_zero, map_zero]; exact Ideal.zero_mem _
      smul_mem' := fun c x hx y => by
        rw [smul_eq_mul, ← mul_assoc]; exact hx (y * c) }
  have hle : mO o O ≤ J' := by
    rw [mO, Ideal.map_le_iff_le_comap]
    intro t ht y
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ ht
  intro h1
  have := hle h1 1
  rw [mul_one, hl] at this
  exact (IsLocalRing.maximalIdeal.isMaximal o).ne_top ((Ideal.eq_top_iff_one _).2 this)

/- English proof (translation)
Introduce and unpack `⟨u, rfl⟩`. Apply `mO_ne_top hU` to reduce the goal to its premises. Use `Ideal.mul_mem_left (mO o O) ((u⁻¹ : Oˣ) : O) hx` as an intermediate fact. Rewrite `this` using `[Units.inv_mul]`. Then use the resulting hypothesis.
-/
lemma not_unit_of_mem_mO (hU : Unram o O) (x : O) (hx : x ∈ mO o O) : ¬ IsUnit x := by
  rintro ⟨u, rfl⟩
  apply mO_ne_top hU
  have := Ideal.mul_mem_left (mO o O) ((u⁻¹ : Oˣ) : O) hx
  rwa [Units.inv_mul] at this

/- English proof (translation)
Use `hU.free` as an intermediate fact. Establish `: Module.Finite o O` using `Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)`. Set `b` to `Module.Free.chooseBasis o O`. Rewrite using `[← b.sum_repr z]`. Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Take `⟨bi, hbi⟩` from `hU.tr_perfect (b.coord i)`. Establish `h1` using `hbi z`. Rewrite `h1` using `[mul_comm z (star bi), ← hT, Module.Basis.coord_apply]`. Rewrite using `[Algebra.smul_def, h1]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hz _))`.
-/
lemma mem_mO_of_trace (hU : Unram o O) (T : O →ₗ[o] o) (hT : ∀ a, algebraMap o O (T a) = a + star a)
    (z : O) (hz : ∀ s, T (s * z) ∈ IsLocalRing.maximalIdeal o) : z ∈ mO o O := by
  classical
  have := hU.free
  have : Module.Finite o O := Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)
  let b := Module.Free.chooseBasis o O
  rw [← b.sum_repr z]
  refine Ideal.sum_mem _ fun i _ => ?_
  obtain ⟨bi, hbi⟩ := hU.tr_perfect (b.coord i)
  have h1 := hbi z
  rw [mul_comm z (star bi), ← hT, Module.Basis.coord_apply] at h1
  rw [Algebra.smul_def, h1]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hz _))

/- English proof (translation)
Take `⟨T, hT⟩` from `unram_trace hU`. Establish `hnorm : ∀ c ∈ C, ∃ t ∈ IsLocalRing.maximalIdeal o, algebraMap o O t = h c c`. Introduce `c hc`. Take `⟨t, ht⟩` from `unram_fixed hU (h c c) (hH c c).symm`. Use `⟨t, ?_, ht⟩` and prove the remaining obligations.

Rewrite using `[IsLocalRing.mem_maximalIdeal]`. Introduce `hu`. Conclude with `hC c hc (ht ▸ hu.map (algebraMap o O))`. Introduce `c hc c' hc'`. Apply `mem_mO_of_trace hU T hT` to reduce the goal to its premises.

Introduce `s`. Take `⟨t1, ht1, e1⟩` from `hnorm (s • c + c') (C.add_mem (C.smul_mem s hc) hc')`. Take `⟨t2, ht2, e2⟩` from `hnorm (s • c) (C.smul_mem s hc)`. Take `⟨t3, ht3, e3⟩` from `hnorm c' hc'`. Establish `: T (s * h c c') = t1 - t2 - t3`.

Apply `unram_inj hU` to reduce the goal to its premises. Rewrite using `[hT, map_sub, map_sub, e1, e2, e3]`. Establish `e4 : h c' (s • c) = star (s * h c c')`. Rewrite using `[hH (s • c) c', map_smul, LinearMap.smul_apply, smul_eq_mul]`. Simplify using `only [map_add, LinearMap.add_apply, e4]`.

Simplify using `only [map_smul, LinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Ideal.sub_mem _ (Ideal.sub_mem _ ht1 ht2) ht3`.
-/
lemma polar_mO (hU : Unram o O) {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂]
    (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O) (hH : IsHerm h) (C : Submodule O abelian₂)
    (hC : ∀ c ∈ C, ¬ IsUnit (h c c)) : ∀ c ∈ C, ∀ c' ∈ C, h c c' ∈ mO o O := by
  obtain ⟨T, hT⟩ := unram_trace hU
  have hnorm : ∀ c ∈ C, ∃ t ∈ IsLocalRing.maximalIdeal o, algebraMap o O t = h c c := by
    intro c hc
    obtain ⟨t, ht⟩ := unram_fixed hU (h c c) (hH c c).symm
    refine ⟨t, ?_, ht⟩
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    exact hC c hc (ht ▸ hu.map (algebraMap o O))
  intro c hc c' hc'
  apply mem_mO_of_trace hU T hT
  intro s
  obtain ⟨t1, ht1, e1⟩ := hnorm (s • c + c') (C.add_mem (C.smul_mem s hc) hc')
  obtain ⟨t2, ht2, e2⟩ := hnorm (s • c) (C.smul_mem s hc)
  obtain ⟨t3, ht3, e3⟩ := hnorm c' hc'
  have : T (s * h c c') = t1 - t2 - t3 := by
    apply unram_inj hU
    rw [hT, map_sub, map_sub, e1, e2, e3]
    have e4 : h c' (s • c) = star (s * h c c') := by
      rw [hH (s • c) c', map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp only [map_add, LinearMap.add_apply, e4]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.sub_mem _ ht1 ht2) ht3

end unram2

section orth
variable {O : Type} [CommRing O] [StarRing O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂]
  (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)

/- English proof (translation)
Rewrite using `[map_sum, Finset.sum_eq_single j]`. Rewrite using `[LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul]`. Introduce `i _ hi`. Rewrite using `[LinearMap.map_smulₛₗ, horth j i (Ne.symm hi), smul_zero]`. Introduce `hj`.

Conclude with `absurd (Finset.mem_univ _) hj`.
-/
lemma orth_pair_right {κ : Type} [Fintype κ] (v : κ → abelian₂) (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0)
    (j : κ) (w : κ → O) : h (v j) (∑ i, w i • v i) = star (w j) * h (v j) (v j) := by
  rw [map_sum, Finset.sum_eq_single j]
  · rw [LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul]
  · intro i _ hi
    rw [LinearMap.map_smulₛₗ, horth j i (Ne.symm hi), smul_zero]
  · intro hj; exact absurd (Finset.mem_univ _) hj

/- English proof (translation)
Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by`. Rewrite using `[LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul]`.
-/
lemma orth_pair_gen {κ : Type} [Fintype κ] (v : κ → abelian₂) (x : abelian₂) (w : κ → O) :
    h x (∑ i, w i • v i) = ∑ i, star (w i) * h x (v i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul]

/- English proof (translation)
Rewrite using `[map_sum, LinearMap.sum_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_smul, LinearMap.smul_apply, smul_eq_mul]`.
-/
lemma orth_pair_left {κ : Type} [Fintype κ] (v : κ → abelian₂) (x : abelian₂) (w : κ → O) :
    h (∑ i, w i • v i) x = ∑ i, w i * h (v i) x := by
  rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

/- English proof (translation)
Rewrite using `[map_sub, LinearMap.sub_apply, orth_pair_left, Finset.sum_eq_single j]`. Rewrite using `[← hu, mul_assoc, Units.inv_mul, mul_one, sub_self]`. Introduce `i _ hi`. Rewrite using `[horth i j hi, mul_zero]`. Introduce `hj`.

Conclude with `absurd (Finset.mem_univ _) hj`.
-/
lemma orth_proj {κ : Type} [Fintype κ] (v : κ → abelian₂) (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0)
    (u : κ → Oˣ) (hu : ∀ i, (u i : O) = h (v i) (v i)) (x : abelian₂) (j : κ) :
    h (x - ∑ i, (h x (v i) * ((u i)⁻¹ : Oˣ)) • v i) (v j) = 0 := by
  rw [map_sub, LinearMap.sub_apply, orth_pair_left, Finset.sum_eq_single j]
  · rw [← hu, mul_assoc, Units.inv_mul, mul_one, sub_self]
  · intro i _ hi
    rw [horth i j hi, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ _) hj

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg j`. Establish `h1 : h (∑ i, g i • v i) (v j) = 0` using `by rw [hg]; simp`. Rewrite `h1` using `[orth_pair_left, Finset.sum_eq_single j (fun i _ hi => by rw [horth i j hi, mul_zero]) (fun hj => absurd (Finset.mem_univ _) hj)]`. Conclude with `(hunit j).mul_left_eq_zero.1 h1`.
-/
lemma orth_li {κ : Type} [Fintype κ] (v : κ → abelian₂) (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0)
    (hunit : ∀ i, IsUnit (h (v i) (v i))) : LinearIndependent O v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h1 : h (∑ i, g i • v i) (v j) = 0 := by rw [hg]; simp
  rw [orth_pair_left, Finset.sum_eq_single j (fun i _ hi => by rw [horth i j hi, mul_zero])
    (fun hj => absurd (Finset.mem_univ _) hj)] at h1
  exact (hunit j).mul_left_eq_zero.1 h1

/- English proof (translation)
Establish `hli` using `orth_li h v horth hunit`. Use `choose u hu using hunit`. Establish `hmem : ∀ i, v i ∈ Submodule.span O (Set.range v)` using `fun i => Submodule.subset_span ⟨i, rfl⟩`. Use `⟨Module.Free.of_basis (Module.Basis.span hli), ?_, fun x => ?_, fun φ => ?_⟩` and prove the remaining obligations. Rewrite using `[finrank_span_eq_card hli]`.

Use `⟨∑ i, (h x (v i) * ((u i)⁻¹ : Oˣ)) • v i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i), fun t' ht' => ?_⟩` and prove the remaining obligations. Take `⟨w, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 ht'`. Rewrite using `[orth_pair_gen]`. Conclude with `Finset.sum_eq_zero fun j _ => by rw [orth_proj h v horth u hu, mul_zero]`. Use `⟨∑ i, star (φ ⟨v i, hmem i⟩ * ((u i)⁻¹ : Oˣ)) • v i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i), fun x => ?_⟩` and prove the remaining obligations.

Take `⟨w, hw⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 x.2`. Establish `hx : x = ∑ j, w j • (⟨v j, hmem j⟩ : Submodule.span O (Set.range v))`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hw]`. Simplify using the standard rewrite rules.

Rewrite using `[← hw, orth_pair_left]`. Use `conv_lhs => rw [hx, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, orth_pair_right h v horth, star_star, ← hu, mul_assoc, Units.inv_mul, mul_one]`.
-/
lemma orth_span [Nontrivial O] {κ : Type} [Fintype κ] (v : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i))) :
    Module.Free O (Submodule.span O (Set.range v)) ∧
    Module.finrank O (Submodule.span O (Set.range v)) = Fintype.card κ ∧
    (∀ x, ∃ t ∈ Submodule.span O (Set.range v), ∀ t' ∈ Submodule.span O (Set.range v),
      h (x - t) t' = 0) ∧
    (∀ φ : Submodule.span O (Set.range v) →ₗ[O] O, ∃ w ∈ Submodule.span O (Set.range v),
      ∀ x : Submodule.span O (Set.range v), φ x = h x w) := by
  have hli := orth_li h v horth hunit
  choose u hu using hunit
  have hmem : ∀ i, v i ∈ Submodule.span O (Set.range v) := fun i => Submodule.subset_span ⟨i, rfl⟩
  refine ⟨Module.Free.of_basis (Module.Basis.span hli), ?_, fun x => ?_, fun φ => ?_⟩
  · rw [finrank_span_eq_card hli]
  · refine ⟨∑ i, (h x (v i) * ((u i)⁻¹ : Oˣ)) • v i,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i), fun t' ht' => ?_⟩
    obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 ht'
    rw [orth_pair_gen]
    exact Finset.sum_eq_zero fun j _ => by rw [orth_proj h v horth u hu, mul_zero]
  · refine ⟨∑ i, star (φ ⟨v i, hmem i⟩ * ((u i)⁻¹ : Oˣ)) • v i,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i), fun x => ?_⟩
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 x.2
    have hx : x = ∑ j, w j • (⟨v j, hmem j⟩ : Submodule.span O (Set.range v)) := by
      apply Subtype.ext
      rw [← hw]
      simp
    rw [← hw, orth_pair_left]
    conv_lhs => rw [hx, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, orth_pair_right h v horth, star_star, ← hu, mul_assoc,
      Units.inv_mul, mul_one]

end orth

section unimod
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis O abelian₂`. Establish `hw : ∀ i, ∃ w, ∀ x, b.coord i x = h x w` using `fun i => hSD.2 (b.coord i)`. Use `choose w hw using hw`. Set `Pst : Matrix (Module.Free.ChooseBasisIndex O abelian₂) (Module.Free.ChooseBasisIndex O abelian₂) O` to `Matrix.of fun l i => star (b.repr (w i) l)`. Establish `hmul : (Matrix.of fun i l => h (b i) (b l)) * Pst = 1`.

Use extensionality with `j i`. Rewrite using `[Matrix.mul_apply]`. Establish `h1 : h (b j) (w i) = ∑ l, h (b j) (b l) * star (b.repr (w i) l)` using `by conv_lhs => rw [← b.sum_repr (w i), map_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by`. Rewrite using `[LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul, mul_comm]`.

Establish `h3 : h (b j) (w i) = if j = i then 1 else 0`. Rewrite using `[← hw, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Simplify using `only [Matrix.of_apply, Pst]`. Rewrite using `[← h1, h3, Matrix.one_apply]`. Use `congrArg Matrix.det hmul` as an intermediate fact.

Rewrite `this` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `IsUnit.of_mul_eq_one _ this`.
-/
lemma gram_unit (hSD : SelfDual h) :
    IsUnit (Matrix.of fun i l : Module.Free.ChooseBasisIndex O abelian₂ =>
      h (Module.Free.chooseBasis O abelian₂ i) (Module.Free.chooseBasis O abelian₂ l)).det := by
  classical
  let b := Module.Free.chooseBasis O abelian₂
  have hw : ∀ i, ∃ w, ∀ x, b.coord i x = h x w := fun i => hSD.2 (b.coord i)
  choose w hw using hw
  let Pst : Matrix (Module.Free.ChooseBasisIndex O abelian₂) (Module.Free.ChooseBasisIndex O abelian₂) O :=
    Matrix.of fun l i => star (b.repr (w i) l)
  have hmul : (Matrix.of fun i l => h (b i) (b l)) * Pst = 1 := by
    ext j i
    rw [Matrix.mul_apply]
    have h1 : h (b j) (w i) = ∑ l, h (b j) (b l) * star (b.repr (w i) l) := by
      conv_lhs => rw [← b.sum_repr (w i), map_sum]
      exact Finset.sum_congr rfl fun l _ => by
        rw [LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul, mul_comm]
    have h3 : h (b j) (w i) = if j = i then 1 else 0 := by
      rw [← hw, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [Matrix.of_apply, Pst]
    rw [← h1, h3, Matrix.one_apply]
  have := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact IsUnit.of_mul_eq_one _ this

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hH` using `hSD.1`. Set `C : Submodule O abelian₂` to `{ carrier := {c | ∀ i, h c (v i) = 0} add_mem' := fun {a b} ha hb i => by rw [map_add, LinearMap.add_apply, ha i, hb i, add_zero] zero_mem' := fun i => by simp smul_mem' := fun r c hc i => by rw [map_smul, LinearMap.smul_apply, hc i, smul_zero] }`. Establish `hCJ` using `hpol C (fun c hc => hcon c hc)`.

Set `b` to `Module.Free.chooseBasis O abelian₂`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex O abelian₂) = Module.finrank O abelian₂` using `(Module.finrank_eq_card_chooseBasisIndex O abelian₂).symm`. Use `choose u hu using hunit`. Set `a : Module.Free.ChooseBasisIndex O abelian₂ → κ → O` to `fun i j => h (b i) (v j) * ((u j)⁻¹ : Oˣ)`. Set `cc : Module.Free.ChooseBasisIndex O abelian₂ → abelian₂` to `fun i => b i - ∑ j, a i j • v j`.

Establish `hcc : ∀ i, cc i ∈ C` using `fun i j => orth_proj h v horth u hu (b i) j`. Establish `hbi : ∀ i, b i = cc i + ∑ j, a i j • v j` using `fun i => by simp [cc]`. Establish `hG : ∀ i l, h (b i) (b l) = ∑ j, a i j * ((u j : O) * star (a l j)) + h (cc i) (cc l)`. Introduce `i l`. Establish `e1 : h (cc i) (∑ j, a l j • v j) = 0`.

Rewrite using `[orth_pair_gen]; exact Finset.sum_eq_zero fun j _ => by rw [hcc i j, mul_zero]`. Establish `e2 : h (∑ j, a i j • v j) (cc l) = 0`. Rewrite using `[orth_pair_left]`. Conclude with `Finset.sum_eq_zero fun j _ => by rw [hH (cc l) (v j), hcc l j, star_zero, mul_zero]`. Establish `e3 : h (∑ j, a i j • v j) (∑ j, a l j • v j) = ∑ j, a i j * ((u j : O) * star (a l j))`.

Rewrite using `[orth_pair_left]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [orth_pair_right h v horth, hu, mul_comm (star _)]`. Use `conv_lhs => rw [hbi i, hbi l]`. Rewrite using `[map_add (h _), map_add h, LinearMap.add_apply, LinearMap.add_apply, e1, e2, e3]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hdet` using `gram_unit h hSD`. Apply `hJ _ _ hdet` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det]`. Set `A : Matrix (Module.Free.ChooseBasisIndex O abelian₂) κ O` to `Matrix.of a`. Set `B : Matrix κ (Module.Free.ChooseBasisIndex O abelian₂) O` to `Matrix.of fun j l => (u j : O) * star (a l j)`.

Establish `hmap : (Ideal.Quotient.mk J).mapMatrix (Matrix.of fun i l => h (b i) (b l)) = (A.map (Ideal.Quotient.mk J)) * (B.map (Ideal.Quotient.mk J))`. Rewrite using `[← Matrix.map_mul]`. Use extensionality with `i l`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, A, B]`. Rewrite using `[hG i l, map_add, (Ideal.Quotient.eq_zero_iff_mem).2 (hCJ _ (hcc i) _ (hcc l)), add_zero]`.

Rewrite using `[hmap]`. Apply `det_mul_eq_zero_of_card_lt` to reduce the goal to its premises. Rewrite using `[hcard]`. Conclude with `hk`.
-/
lemma exists_unit_vec_gen [Nontrivial O] (J : Ideal O) (hJ : ∀ x ∈ J, ¬ IsUnit x)
    (hpol : ∀ C : Submodule O abelian₂, (∀ c ∈ C, ¬ IsUnit (h c c)) → ∀ c ∈ C, ∀ c' ∈ C, h c c' ∈ J)
    (hSD : SelfDual h) {κ : Type} [Fintype κ] (v : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i)))
    (hk : Fintype.card κ < Module.finrank O abelian₂) : ∃ c, (∀ i, h c (v i) = 0) ∧ IsUnit (h c c) := by
  classical
  by_contra hcon
  push Not at hcon
  have hH := hSD.1
  let C : Submodule O abelian₂ :=
    { carrier := {c | ∀ i, h c (v i) = 0}
      add_mem' := fun {a b} ha hb i => by rw [map_add, LinearMap.add_apply, ha i, hb i, add_zero]
      zero_mem' := fun i => by simp
      smul_mem' := fun r c hc i => by rw [map_smul, LinearMap.smul_apply, hc i, smul_zero] }
  have hCJ := hpol C (fun c hc => hcon c hc)
  let b := Module.Free.chooseBasis O abelian₂
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex O abelian₂) = Module.finrank O abelian₂ :=
    (Module.finrank_eq_card_chooseBasisIndex O abelian₂).symm
  choose u hu using hunit
  let a : Module.Free.ChooseBasisIndex O abelian₂ → κ → O := fun i j => h (b i) (v j) * ((u j)⁻¹ : Oˣ)
  let cc : Module.Free.ChooseBasisIndex O abelian₂ → abelian₂ := fun i => b i - ∑ j, a i j • v j
  have hcc : ∀ i, cc i ∈ C := fun i j => orth_proj h v horth u hu (b i) j
  have hbi : ∀ i, b i = cc i + ∑ j, a i j • v j := fun i => by simp [cc]
  have hG : ∀ i l, h (b i) (b l) = ∑ j, a i j * ((u j : O) * star (a l j)) + h (cc i) (cc l) := by
    intro i l
    have e1 : h (cc i) (∑ j, a l j • v j) = 0 := by
      rw [orth_pair_gen]; exact Finset.sum_eq_zero fun j _ => by rw [hcc i j, mul_zero]
    have e2 : h (∑ j, a i j • v j) (cc l) = 0 := by
      rw [orth_pair_left]
      exact Finset.sum_eq_zero fun j _ => by rw [hH (cc l) (v j), hcc l j, star_zero, mul_zero]
    have e3 : h (∑ j, a i j • v j) (∑ j, a l j • v j) = ∑ j, a i j * ((u j : O) * star (a l j)) := by
      rw [orth_pair_left]
      exact Finset.sum_congr rfl fun j _ => by rw [orth_pair_right h v horth, hu, mul_comm (star _)]
    conv_lhs => rw [hbi i, hbi l]
    rw [map_add (h _), map_add h, LinearMap.add_apply, LinearMap.add_apply, e1, e2, e3]
    ring
  have hdet := gram_unit h hSD
  apply hJ _ _ hdet
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det]
  let A : Matrix (Module.Free.ChooseBasisIndex O abelian₂) κ O := Matrix.of a
  let B : Matrix κ (Module.Free.ChooseBasisIndex O abelian₂) O :=
    Matrix.of fun j l => (u j : O) * star (a l j)
  have hmap : (Ideal.Quotient.mk J).mapMatrix (Matrix.of fun i l => h (b i) (b l))
      = (A.map (Ideal.Quotient.mk J)) * (B.map (Ideal.Quotient.mk J)) := by
    rw [← Matrix.map_mul]
    ext i l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, A, B]
    rw [hG i l, map_add, (Ideal.Quotient.eq_zero_iff_mem).2 (hCJ _ (hcc i) _ (hcc l)), add_zero]
  rw [hmap]
  apply det_mul_eq_zero_of_card_lt
  rw [hcard]
  exact hk

/- English proof (translation)
Establish `: Nontrivial O` using `Module.nontrivial_of_finrank_pos (R := o) (by rw [hU.rank2]; norm_num)`. Conclude with `exists_unit_vec_gen h (mO o O) (not_unit_of_mem_mO hU) (polar_mO hU h hSD.1) hSD v horth hunit hk`.
-/
lemma exists_unit_vec (hU : Unram o O) (hSD : SelfDual h) {κ : Type} [Fintype κ] (v : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i)))
    (hk : Fintype.card κ < Module.finrank O abelian₂) : ∃ c, (∀ i, h c (v i) = 0) ∧ IsUnit (h c c) := by
  have : Nontrivial O := Module.nontrivial_of_finrank_pos (R := o) (by rw [hU.rank2]; norm_num)
  exact exists_unit_vec_gen h (mO o O) (not_unit_of_mem_mO hU) (polar_mO hU h hSD.1) hSD v horth hunit hk

/- English proof (translation)
Proceed by induction on `ρ with`. Consider the case `zero => exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩`. Consider the case `succ k ih`. Take `⟨v, horth, hunit⟩` from `ih (by omega)`. Take `⟨c, hc, hcu⟩` from `exists_unit_vec_gen h J hJ hpol hSD v horth hunit (by rw [Fintype.card_fin]; omega)`.

Use `⟨Fin.cons c v, fun i j => ?_, fun i => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j`. Introduce `hne`. Conclude with `absurd rfl hne`. Introduce `_`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Conclude with `hc j`. Introduce `_`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[hSD.1 c (v i), hc i, star_zero]`.

Introduce `hne`. Simplify using `only [Fin.cons_succ]`. Conclude with `horth i j (fun e => hne (by rw [e]))`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `using hcu`.

Simplify using `using hunit i`.
-/
lemma exists_orth_family_gen [Nontrivial O] (J : Ideal O) (hJ : ∀ x ∈ J, ¬ IsUnit x)
    (hpol : ∀ C : Submodule O abelian₂, (∀ c ∈ C, ¬ IsUnit (h c c)) → ∀ c ∈ C, ∀ c' ∈ C, h c c' ∈ J)
    (hSD : SelfDual h) (ρ : ℕ) (hρ : ρ ≤ Module.finrank O abelian₂) :
    ∃ v : Fin ρ → abelian₂, (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, IsUnit (h (v i) (v i)) := by
  induction ρ with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨v, horth, hunit⟩ := ih (by omega)
    obtain ⟨c, hc, hcu⟩ := exists_unit_vec_gen h J hJ hpol hSD v horth hunit (by rw [Fintype.card_fin]; omega)
    refine ⟨Fin.cons c v, fun i j => ?_, fun i => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro hne; exact absurd rfl hne
      · intro _; simp only [Fin.cons_zero, Fin.cons_succ]; exact hc j
      · intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hSD.1 c (v i), hc i, star_zero]
      · intro hne
        simp only [Fin.cons_succ]
        exact horth i j (fun e => hne (by rw [e]))
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hcu
      · simpa using hunit i

end unimod

/- English proof (translation)
Introduce `o O abelian₂ _ _ _ _ _ _ _ _ _ _ h hU hSD ρ hρ`. Establish `: Nontrivial O` using `Module.nontrivial_of_finrank_pos (R := o) (by rw [hU.rank2]; norm_num)`. Take `⟨v, horth, hunit⟩` from `exists_orth_family_gen h (mO o O) (not_unit_of_mem_mO hU) (polar_mO hU h hSD.1) hSD ρ hρ`. Take `⟨h1, h3, h4, h5⟩` from `orth_span h v horth hunit`. Conclude with `⟨Submodule.span O (Set.range v), h1, by rw [h3, Fintype.card_fin], h4, h5⟩`.
-/
theorem unimodular_rank : UnimodRank := by
  intro o O abelian₂ _ _ _ _ _ _ _ _ _ _ h hU hSD ρ hρ
  have : Nontrivial O := Module.nontrivial_of_finrank_pos (R := o) (by rw [hU.rank2]; norm_num)
  obtain ⟨v, horth, hunit⟩ := exists_orth_family_gen h (mO o O) (not_unit_of_mem_mO hU)
    (polar_mO hU h hSD.1) hSD ρ hρ
  obtain ⟨h1, h3, h4, h5⟩ := orth_span h v horth hunit
  exact ⟨Submodule.span O (Set.range v), h1, by rw [h3, Fintype.card_fin], h4, h5⟩

section unimod2
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩`. Consider the case `succ k ih`. Take `⟨t, htu, hto, htn⟩` from `ih (by omega)`. Take `⟨c, hc, hcu⟩` from `exists_unit_vec h hU hSD (Sum.elim u t) (by`.

Introduce and unpack `(i | i) (j | j) hne`. Conclude with `horth i j (fun e => hne (by rw [e]))`. Simplify using `only [Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[hSD.1 (t j) (u i), htu, star_zero]`. Conclude with `htu i j`.

Conclude with `hto i j (fun e => hne (by rw [e])))`. Use the proof step `(by rintro (i | i); exacts [hunit i, htn i])`. Use the proof step `(by rw [Fintype.card_sum, Fintype.card_fin]; omega)`. Use `⟨Fin.cons c t, fun i j => ?_, fun i j => ?_, fun i => ?_⟩` and prove the remaining obligations. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations.

Simplify using `using hc (Sum.inl j)`. Simplify using `using htu i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j`. Introduce `hne`. Conclude with `absurd rfl hne`.

Introduce `_`. Simplify using `using hc (Sum.inr j)`. Introduce `_`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[hSD.1 c (t i)]`.

Use `hc (Sum.inr i)` as an intermediate fact. Simplify using `only [Sum.elim_inr] at this`. Rewrite using `[this, star_zero]`. Introduce `hne`. Simplify using `only [Fin.cons_succ]`.

Conclude with `hto i j (fun e => hne (by rw [e]))`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `using hcu`. Simplify using `using htn i`.
-/
lemma extend_family (hU : Unram o O) (hSD : SelfDual h) {κ : Type} [Fintype κ] (u : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (u i) (u j) = 0) (hunit : ∀ i, IsUnit (h (u i) (u i))) (r : ℕ)
    (hr : Fintype.card κ + r ≤ Module.finrank O abelian₂) :
    ∃ t : Fin r → abelian₂, (∀ i j, h (t i) (u j) = 0) ∧ (∀ i j, i ≠ j → h (t i) (t j) = 0) ∧
      ∀ i, IsUnit (h (t i) (t i)) := by
  induction r with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨t, htu, hto, htn⟩ := ih (by omega)
    obtain ⟨c, hc, hcu⟩ := exists_unit_vec h hU hSD (Sum.elim u t)
      (by
        rintro (i | i) (j | j) hne
        · exact horth i j (fun e => hne (by rw [e]))
        · simp only [Sum.elim_inl, Sum.elim_inr]; rw [hSD.1 (t j) (u i), htu, star_zero]
        · exact htu i j
        · exact hto i j (fun e => hne (by rw [e])))
      (by rintro (i | i); exacts [hunit i, htn i])
      (by rw [Fintype.card_sum, Fintype.card_fin]; omega)
    refine ⟨Fin.cons c t, fun i j => ?_, fun i j => ?_, fun i => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hc (Sum.inl j)
      · simpa using htu i j
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro hne; exact absurd rfl hne
      · intro _; simpa using hc (Sum.inr j)
      · intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hSD.1 c (t i)]
        have := hc (Sum.inr i)
        simp only [Sum.elim_inr] at this
        rw [this, star_zero]
      · intro hne
        simp only [Fin.cons_succ]
        exact hto i j (fun e => hne (by rw [e]))
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hcu
      · simpa using htn i

omit [IsDomain o] [IsDiscreteValuationRing o] [Algebra o O] [CommRing o] in
/- English proof (translation)
Set `b` to `Module.Free.chooseBasis O abelian₂`. Set `M : Matrix (Module.Free.ChooseBasisIndex O abelian₂) (Module.Free.ChooseBasisIndex O abelian₂) O` to `Matrix.of fun i l => b.repr (v i) l`. Set `G : Matrix (Module.Free.ChooseBasisIndex O abelian₂) (Module.Free.ChooseBasisIndex O abelian₂) O` to `Matrix.of fun l l' => h (b l) (b l')`. Establish `hv : ∀ i, v i = ∑ l, M i l • b l` using `fun i => (b.sum_repr (v i)).symm`. Establish `hD : M * G * M.conjTranspose = Matrix.diagonal fun i => h (v i) (v i)`.

Use extensionality with `i i'`. Establish `e1 : h (v i) (v i') = ∑ l', (∑ l, M i l * G l l') * star (M i' l')` using `by conv_lhs => rw [hv i, hv i']`. Rewrite using `[orth_pair_gen]`. Use `Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Rewrite using `[orth_pair_left, mul_comm]`.

Both sides reduce to the same expression. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply]`. Rewrite using `[← e1, Matrix.diagonal_apply]`. Use `split_ifs with hii`.

Rewrite using `[hii]`. Conclude with `horth i i' hii`. Establish `hdet : IsUnit M.det`. Establish `h1 : IsUnit (M * G * M.conjTranspose).det`. Rewrite using `[hD, Matrix.det_diagonal]`.

Conclude with `IsUnit.prod_univ_iff.2 hunit`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, mul_assoc]`. Conclude with `isUnit_of_mul_isUnit_left h1`. Rewrite using `[eq_top_iff, ← b.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨l, rfl⟩`.

Establish `: b l = ∑ i, M⁻¹ l i • v i`. Establish `e2 : ∑ i, M⁻¹ l i • v i = ∑ l', (M⁻¹ * M) l l' • b l'`. Simplify using `only [Matrix.mul_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hv i, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun l' _ => by rw [smul_smul]`. Rewrite using `[e2, Matrix.nonsing_inv_mul M hdet]`. Simplify using `[Matrix.one_apply]`. Rewrite using `[this]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
lemma span_orthogonal_unit_basis_eq_top (v : Module.Free.ChooseBasisIndex O abelian₂ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i))) :
    Submodule.span O (Set.range v) = ⊤ := by
  classical
  let b := Module.Free.chooseBasis O abelian₂
  let M : Matrix (Module.Free.ChooseBasisIndex O abelian₂) (Module.Free.ChooseBasisIndex O abelian₂) O :=
    Matrix.of fun i l => b.repr (v i) l
  let G : Matrix (Module.Free.ChooseBasisIndex O abelian₂) (Module.Free.ChooseBasisIndex O abelian₂) O :=
    Matrix.of fun l l' => h (b l) (b l')
  have hv : ∀ i, v i = ∑ l, M i l • b l := fun i => (b.sum_repr (v i)).symm
  have hD : M * G * M.conjTranspose = Matrix.diagonal fun i => h (v i) (v i) := by
    ext i i'
    have e1 : h (v i) (v i') = ∑ l', (∑ l, M i l * G l l') * star (M i' l') := by
      conv_lhs => rw [hv i, hv i']
      rw [orth_pair_gen]
      refine Finset.sum_congr rfl fun l' _ => ?_
      rw [orth_pair_left, mul_comm]
      rfl
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [← e1, Matrix.diagonal_apply]
    split_ifs with hii
    · rw [hii]
    · exact horth i i' hii
  have hdet : IsUnit M.det := by
    have h1 : IsUnit (M * G * M.conjTranspose).det := by
      rw [hD, Matrix.det_diagonal]
      exact IsUnit.prod_univ_iff.2 hunit
    rw [Matrix.det_mul, Matrix.det_mul, mul_assoc] at h1
    exact isUnit_of_mul_isUnit_left h1
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  have : b l = ∑ i, M⁻¹ l i • v i := by
    have e2 : ∑ i, M⁻¹ l i • v i = ∑ l', (M⁻¹ * M) l l' • b l' := by
      simp only [Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hv i, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l' _ => by rw [smul_smul]
    rw [e2, Matrix.nonsing_inv_mul M hdet]
    simp [Matrix.one_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [IsDomain o] [IsDiscreteValuationRing o] [Algebra o O] [CommRing o] in
/- English proof (translation)
Establish `e : Module.Free.ChooseBasisIndex O abelian₂ ≃ κ` using `Fintype.equivOfCardEq (by`. Rewrite using `[hcard, Module.finrank_eq_card_chooseBasisIndex])`. Use `span_orthogonal_unit_basis_eq_top h (v ∘ e) (fun i j hij => horth _ _ (fun hh => hij (e.injective hh))) (fun i => hunit _)` as an intermediate fact. Rewrite `this` using `[e.surjective.range_comp]`. Then use the resulting hypothesis.
-/
lemma full_span [Nontrivial O] {κ : Type} [Fintype κ] (v : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i)))
    (hcard : Fintype.card κ = Module.finrank O abelian₂) : Submodule.span O (Set.range v) = ⊤ := by
  have e : Module.Free.ChooseBasisIndex O abelian₂ ≃ κ := Fintype.equivOfCardEq (by
    rw [hcard, Module.finrank_eq_card_chooseBasisIndex])
  have := span_orthogonal_unit_basis_eq_top h (v ∘ e) (fun i j hij => horth _ _ (fun hh => hij (e.injective hh)))
    (fun i => hunit _)
  rwa [e.surjective.range_comp] at this

end unimod2

/- English proof (translation)
Introduce `o O abelian₂ _ _ _ _ _ _ _ _ _ _ h hU hSD S m₀ hS hSfree hSrank`. Establish `hH` using `hSD.1`. Establish `: Nontrivial O` using `Module.nontrivial_of_finrank_pos (R := o) (by rw [hU.rank2]; norm_num)`. Use `hU.free` as an intermediate fact. Establish `: Module.Finite o O` using `Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)`.

Establish `: IsNoetherianRing O` using `IsNoetherianRing.of_finite o O`. Establish `: Module.Finite O S` using `inferInstance`. Set `P : ℕ → Prop` to `fun p => ∃ u : Fin p → abelian₂, (∀ i, ∀ s ∈ S, h (u i) s = 0) ∧ (∀ i j, i ≠ j → h (u i) (u j) = 0) ∧ ∀ i, IsUnit (h (u i) (u i))`. Establish `hP0 : P 0` using `⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩`. Establish `hPle : ∀ p, P p → p ≤ Module.finrank O abelian₂`.

Introduce and unpack `p ⟨u, _, huo, huu⟩`. Use `(orth_li h u huo huu).fintype_card_le_finrank` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`. Then use the resulting hypothesis. Choose the witnesses or unpack the hypotheses as in `⟨p, hp, hmax⟩ : ∃ p, P p ∧ ¬ P (p + 1) := by`. Use `⟨Nat.findGreatest P (Module.finrank O abelian₂), Nat.findGreatest_spec (Nat.zero_le _) hP0, ?_⟩` and prove the remaining obligations.

Introduce `hq`. Conclude with `Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hPle _ hq) hq`. Establish `hpn` using `hPle p hp`. Take `⟨u, huS, huo, huu⟩` from `hp`. Set `N' : Submodule O abelian₂` to `{ carrier := {c | (∀ s ∈ S, h c s = 0) ∧ ∀ i, h c (u i) = 0} add_mem' := fun {a b} ha hb => ⟨fun s hs => by`.

Rewrite using `[map_add, LinearMap.add_apply, ha.1 s hs, hb.1 s hs, add_zero], fun i => by`. Rewrite using `[map_add, LinearMap.add_apply, ha.2 i, hb.2 i, add_zero]⟩`. Use the proof step `zero_mem' := ⟨fun s _ => by simp, fun i => by simp⟩`. Use the proof step `smul_mem' := fun r c hc => ⟨fun s hs => by`. Rewrite using `[map_smul, LinearMap.smul_apply, hc.1 s hs, smul_zero], fun i => by`.

Rewrite using `[map_smul, LinearMap.smul_apply, hc.2 i, smul_zero]⟩ }`. Establish `hN' : ∀ c ∈ N', ¬ IsUnit (h c c)`. Introduce `c hc hcu`. Apply `hmax` to reduce the goal to its premises. Use `⟨Fin.cons c u, fun i => ?_, fun i j => ?_, fun i => ?_⟩` and prove the remaining obligations.

Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `using hc.1`. Simplify using `using huS i`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j`. Introduce `hne`.

Conclude with `absurd rfl hne`. Introduce `_`. Simplify using `using hc.2 j`. Introduce `_`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`.

Rewrite using `[hH c (u i), hc.2 i, star_zero]`. Introduce `hne`. Simplify using `only [Fin.cons_succ]`. Conclude with `huo i j (fun e => hne (by rw [e]))`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations.

Simplify using `using hcu`. Simplify using `using huu i`. Establish `hJ` using `polar_mO hU h hH N' hN'`. Take `⟨r, hr⟩ : ∃ r, p + r = Module.finrank O abelian₂` from `⟨Module.finrank O abelian₂ - p, by omega⟩`. Take `⟨t, htu, hto, htn⟩` from `extend_family h hU hSD u huo huu r (by rw [Fintype.card_fin]; omega)`.

Establish `hut : ∀ i j, h (u i) (t j) = 0` using `fun i j => by rw [hH (t j) (u i), htu, star_zero]`. Establish `hfull : Submodule.span O (Set.range (Sum.elim u t)) = ⊤`. Apply `full_span h` to reduce the goal to its premises. Introduce and unpack `(i | i) (j | j) hne`. Conclude with `huo i j (fun e => hne (by rw [e]))`.

Conclude with `hut i j`. Conclude with `htu i j`. Conclude with `hto i j (fun e => hne (by rw [e]))`. Introduce and unpack `(i | i)`. Use `exacts [huu i, htn i]`.

Rewrite using `[Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hr]`. Establish `hdec : ∀ x : abelian₂, ∃ (a : Fin p → O) (b : Fin r → O), x = ∑ i, a i • u i + ∑ j, b j • t j`. Introduce `x`. Establish `hx : x ∈ Submodule.span O (Set.range (Sum.elim u t))` using `by rw [hfull]; trivial`. Take `⟨cf, hcf⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 hx`.

Use `⟨fun i => cf (Sum.inl i), fun j => cf (Sum.inr j), ?_⟩` and prove the remaining obligations. Rewrite using `[← hcf, Fintype.sum_sum_type]`. Both sides reduce to the same expression. Establish `hmemT : ∀ b : Fin r → O, ∑ j, b j • t j ∈ Submodule.span O (Set.range t)` using `fun b => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Establish `hmemU : ∀ a : Fin p → O, ∑ i, a i • u i ∈ Submodule.span O (Set.range u)` using `fun a => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.

Take `⟨hT1, hT2, hT3, _⟩` from `orth_span h t hto htn`. Take `⟨hU1, hU2, _, hU4⟩` from `orth_span h u huo huu`. Rewrite `hT2`, `hU2` using `[Fintype.card_fin]`. Establish `hsu : ∀ s ∈ S, ∀ i, h s (u i) = 0` using `fun s hs i => by rw [hH (u i) s, huS i s hs, star_zero]`. Establish `hrank : r ≤ 2 * m₀`.

Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Set `bS` to `Module.Free.chooseBasis O S`. Establish `hcardS : Fintype.card (Module.Free.ChooseBasisIndex O S) = m₀`. Rewrite using `[← hSrank, Module.finrank_eq_card_chooseBasisIndex]`.

Set `sv : Module.Free.ChooseBasisIndex O S → abelian₂` to `fun l => (bS l : abelian₂)`. Establish `hsvS : ∀ l, sv l ∈ S` using `fun l => (bS l).2`. Establish `hw0 : ∀ j, ∃ w, ∀ v : S, bS.coord j v = h v w` using `fun j => dual_capacity_formula o O abelian₂ h hU hSD S hS (bS.coord j)`. Use `choose w0 hw0 using hw0`. Use `choose uu huu' using huu`.

Set `w : Module.Free.ChooseBasisIndex O S → abelian₂` to `fun j => w0 j - ∑ i, (h (w0 j) (u i) * ((uu i)⁻¹ : Oˣ)) • u i`. Establish `hwu : ∀ j i, h (w j) (u i) = 0` using `fun j i => orth_proj h u huo uu huu' (w0 j) i`. Establish `hsw : ∀ l j, h (sv l) (w j) = if l = j then 1 else 0`. Introduce `l j`. Establish `e1 : h (sv l) (w j) = h (sv l) (w0 j)`.

Simplify using `only [w]`. Rewrite using `[map_sub, orth_pair_gen]`. Rewrite using `[Finset.sum_eq_zero (fun i _ => by rw [hsu _ (hsvS l) i, mul_zero]), sub_zero]`. Rewrite using `[e1, ← hw0 j (bS l), Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Establish `hws : ∀ j l, h (w j) (sv l) = if l = j then 1 else 0`.

Introduce `j l`. Apply the tactic sequence `rw [hH (sv l) (w j), hsw]; split_ifs <;> simp`. Set `c : Fin r → Module.Free.ChooseBasisIndex O S → O` to `fun i l => h (t i) (sv l)`. Set `nn : Fin r → abelian₂` to `fun i => t i - ∑ l, c i l • w l`. Establish `hnnsv : ∀ i l, h (nn i) (sv l) = 0`.

Introduce `i l`. Simplify using `only [nn]`. Rewrite using `[map_sub, LinearMap.sub_apply, orth_pair_left]`. Simplify using `only [hws, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Simplify using `[c]`.

Establish `hnn : ∀ i, nn i ∈ N'`. Introduce `i`. Use `⟨fun s hs => ?_, fun i' => ?_⟩` and prove the remaining obligations. Establish `es : s = ∑ l, bS.repr ⟨s, hs⟩ l • sv l`. Establish `e0 : ((∑ l, bS.repr ⟨s, hs⟩ l • bS l : S) : abelian₂) = s` using `congrArg Subtype.val (bS.sum_repr ⟨s, hs⟩)`.

Rewrite `e0` using `[Submodule.coe_sum]`. Conclude with `e0.symm`. Rewrite using `[es, orth_pair_gen]`. Conclude with `Finset.sum_eq_zero fun l _ => by rw [hnnsv, mul_zero]`. Simplify using `only [nn]`.

Rewrite using `[map_sub, LinearMap.sub_apply, orth_pair_left, htu]`. Rewrite using `[Finset.sum_eq_zero (fun l _ => by rw [hwu, mul_zero]), sub_zero]`. Establish `hti : ∀ i, t i = ∑ l, c i l • w l + nn i` using `fun i => by simp [nn]`. Establish `hD : ∀ i l, h (t i) (t l) = (∑ j, c i j * h (w j) (t l) + ∑ j, h (nn i) (w j) * star (c l j)) + h (nn i) (nn l)`. Introduce `i l`.

Establish `e1 : h (t i) (t l) = h (∑ j, c i j • w j) (t l) + h (nn i) (t l)` using `by conv_lhs => rw [hti i]`. Rewrite using `[map_add, LinearMap.add_apply]`. Establish `e2 : h (nn i) (t l) = h (nn i) (∑ j, c l j • w j) + h (nn i) (nn l)` using `by conv_lhs => rw [hti l]`. Rewrite using `[map_add]`. Rewrite using `[e1, e2, orth_pair_left, orth_pair_gen, ← add_assoc]`.

Use `congr 2`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Establish `hdetD : IsUnit (Matrix.of fun i l => h (t i) (t l)).det`. Establish `: (Matrix.of fun i l => h (t i) (t l)) = Matrix.diagonal fun i => h (t i) (t i)`. Use extensionality with `i l`.

Rewrite using `[Matrix.diagonal_apply, Matrix.of_apply]`. Use `split_ifs with hil`. Rewrite using `[hil]`. Conclude with `hto i l hil`. Rewrite using `[this, Matrix.det_diagonal]`.

Conclude with `IsUnit.prod_univ_iff.2 htn`. Apply `not_unit_of_mem_mO hU _ _ hdetD` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det]`. Set `A : Matrix (Fin r) (Module.Free.ChooseBasisIndex O S ⊕ Module.Free.ChooseBasisIndex O S) O` to `Matrix.of fun i => Sum.elim (fun j => c i j) (fun j => h (nn i) (w j))`. Set `B : Matrix (Module.Free.ChooseBasisIndex O S ⊕ Module.Free.ChooseBasisIndex O S) (Fin r) O` to `Matrix.of (Sum.elim (fun j l => h (w j) (t l)) (fun j l => star (c l j)))`.

Establish `hmap : (Ideal.Quotient.mk (mO o O)).mapMatrix (Matrix.of fun i l => h (t i) (t l)) = (A.map (Ideal.Quotient.mk (mO o O))) * (B.map (Ideal.Quotient.mk (mO o O)))`. Rewrite using `[← Matrix.map_mul]`. Use extensionality with `i l`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, A, B, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[hD i l, map_add _ (_ + _), (Ideal.Quotient.eq_zero_iff_mem).2 (hJ _ (hnn i) _ (hnn l)), add_zero]`.

Rewrite using `[hmap]`. Apply `det_mul_eq_zero_of_card_lt` to reduce the goal to its premises. Rewrite using `[Fintype.card_sum, Fintype.card_fin, hcardS]`. Use linear arithmetic over natural numbers and integers. Use `⟨Submodule.span O (Set.range t), ?_, hT1, by rw [hT2]; exact hrank, hT3, ?_, Submodule.span O (Set.range u), hU1, by rw [hT2, hU2]; omega, ?_, ?_, hU4⟩` and prove the remaining obligations.

Introduce `s hs`. Take `⟨a, b, hab⟩` from `hdec s`. Establish `ha : ∀ i, a i = 0`. Introduce `i`. Establish `h1` using `hsu s hs i`.

Rewrite `h1` using `[hab, map_add, LinearMap.add_apply, orth_pair_left, orth_pair_left, Finset.sum_eq_zero (fun j _ => by rw [htu, mul_zero] : ∀ j ∈ univ, b j * h (t j) (u i) = 0), add_zero, Finset.sum_eq_single i (fun i' _ hi => by rw [huo i' i hi, mul_zero]) (fun hi => absurd (Finset.mem_univ _) h …`. Conclude with `(huu i).mul_left_eq_zero.1 h1`. Rewrite using `[hab]`. Simplify using `only [ha, zero_smul, Finset.sum_const_zero, zero_add]`. Conclude with `hmemT b`.

Introduce `x hx hx0`. Take `⟨b, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 hx`. Establish `hb : ∀ j, b j = 0`. Introduce `j`. Establish `h1` using `hx0 (t j) (Submodule.subset_span ⟨j, rfl⟩)`.

Rewrite `h1` using `[orth_pair_left, Finset.sum_eq_single j (fun i' _ hi => by rw [hto i' j hi, mul_zero]) (fun hi => absurd (Finset.mem_univ _) hi)]`. Conclude with `(htn j).mul_left_eq_zero.1 h1`. Simplify using `[hb]`. Introduce `x hx y hy`. Take `⟨b, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 hx`.

Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 hy`. Rewrite using `[orth_pair_left]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[orth_pair_gen, Finset.sum_eq_zero (fun i _ => by rw [htu, mul_zero]), mul_zero]`. Introduce `x`.

Take `⟨a, b, hab⟩` from `hdec x`. Conclude with `⟨_, hmemT b, _, hmemU a, by rw [hab, add_comm]⟩`.
-/
theorem unimodular_hull : UnimodHull := by
  intro o O abelian₂ _ _ _ _ _ _ _ _ _ _ h hU hSD S m₀ hS hSfree hSrank
  classical
  have hH := hSD.1
  have : Nontrivial O := Module.nontrivial_of_finrank_pos (R := o) (by rw [hU.rank2]; norm_num)
  have := hU.free
  have : Module.Finite o O := Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)
  have : IsNoetherianRing O := IsNoetherianRing.of_finite o O
  have : Module.Finite O S := inferInstance
  let P : ℕ → Prop := fun p => ∃ u : Fin p → abelian₂, (∀ i, ∀ s ∈ S, h (u i) s = 0) ∧
    (∀ i j, i ≠ j → h (u i) (u j) = 0) ∧ ∀ i, IsUnit (h (u i) (u i))
  have hP0 : P 0 := ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have hPle : ∀ p, P p → p ≤ Module.finrank O abelian₂ := by
    rintro p ⟨u, _, huo, huu⟩
    have := (orth_li h u huo huu).fintype_card_le_finrank
    rwa [Fintype.card_fin] at this
  obtain ⟨p, hp, hmax⟩ : ∃ p, P p ∧ ¬ P (p + 1) := by
    refine ⟨Nat.findGreatest P (Module.finrank O abelian₂), Nat.findGreatest_spec (Nat.zero_le _) hP0, ?_⟩
    intro hq
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hPle _ hq) hq
  have hpn := hPle p hp
  obtain ⟨u, huS, huo, huu⟩ := hp
  let N' : Submodule O abelian₂ :=
    { carrier := {c | (∀ s ∈ S, h c s = 0) ∧ ∀ i, h c (u i) = 0}
      add_mem' := fun {a b} ha hb => ⟨fun s hs => by
          rw [map_add, LinearMap.add_apply, ha.1 s hs, hb.1 s hs, add_zero], fun i => by
          rw [map_add, LinearMap.add_apply, ha.2 i, hb.2 i, add_zero]⟩
      zero_mem' := ⟨fun s _ => by simp, fun i => by simp⟩
      smul_mem' := fun r c hc => ⟨fun s hs => by
          rw [map_smul, LinearMap.smul_apply, hc.1 s hs, smul_zero], fun i => by
          rw [map_smul, LinearMap.smul_apply, hc.2 i, smul_zero]⟩ }
  have hN' : ∀ c ∈ N', ¬ IsUnit (h c c) := by
    intro c hc hcu
    apply hmax
    refine ⟨Fin.cons c u, fun i => ?_, fun i j => ?_, fun i => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hc.1
      · simpa using huS i
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro hne; exact absurd rfl hne
      · intro _; simpa using hc.2 j
      · intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hH c (u i), hc.2 i, star_zero]
      · intro hne
        simp only [Fin.cons_succ]
        exact huo i j (fun e => hne (by rw [e]))
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hcu
      · simpa using huu i
  have hJ := polar_mO hU h hH N' hN'
  obtain ⟨r, hr⟩ : ∃ r, p + r = Module.finrank O abelian₂ := ⟨Module.finrank O abelian₂ - p, by omega⟩
  obtain ⟨t, htu, hto, htn⟩ := extend_family h hU hSD u huo huu r (by rw [Fintype.card_fin]; omega)
  have hut : ∀ i j, h (u i) (t j) = 0 := fun i j => by rw [hH (t j) (u i), htu, star_zero]
  have hfull : Submodule.span O (Set.range (Sum.elim u t)) = ⊤ := by
    apply full_span h
    · rintro (i | i) (j | j) hne
      · exact huo i j (fun e => hne (by rw [e]))
      · exact hut i j
      · exact htu i j
      · exact hto i j (fun e => hne (by rw [e]))
    · rintro (i | i); exacts [huu i, htn i]
    · rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hr]
  have hdec : ∀ x : abelian₂, ∃ (a : Fin p → O) (b : Fin r → O), x = ∑ i, a i • u i + ∑ j, b j • t j := by
    intro x
    have hx : x ∈ Submodule.span O (Set.range (Sum.elim u t)) := by rw [hfull]; trivial
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
    refine ⟨fun i => cf (Sum.inl i), fun j => cf (Sum.inr j), ?_⟩
    rw [← hcf, Fintype.sum_sum_type]
    rfl
  have hmemT : ∀ b : Fin r → O, ∑ j, b j • t j ∈ Submodule.span O (Set.range t) := fun b =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hmemU : ∀ a : Fin p → O, ∑ i, a i • u i ∈ Submodule.span O (Set.range u) := fun a =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨hT1, hT2, hT3, _⟩ := orth_span h t hto htn
  obtain ⟨hU1, hU2, _, hU4⟩ := orth_span h u huo huu
  rw [Fintype.card_fin] at hT2 hU2
  have hsu : ∀ s ∈ S, ∀ i, h s (u i) = 0 := fun s hs i => by rw [hH (u i) s, huS i s hs, star_zero]

  have hrank : r ≤ 2 * m₀ := by
    by_contra hlt
    push Not at hlt
    let bS := Module.Free.chooseBasis O S
    have hcardS : Fintype.card (Module.Free.ChooseBasisIndex O S) = m₀ := by
      rw [← hSrank, Module.finrank_eq_card_chooseBasisIndex]
    let sv : Module.Free.ChooseBasisIndex O S → abelian₂ := fun l => (bS l : abelian₂)
    have hsvS : ∀ l, sv l ∈ S := fun l => (bS l).2
    have hw0 : ∀ j, ∃ w, ∀ v : S, bS.coord j v = h v w := fun j =>
      dual_capacity_formula o O abelian₂ h hU hSD S hS (bS.coord j)
    choose w0 hw0 using hw0
    choose uu huu' using huu
    let w : Module.Free.ChooseBasisIndex O S → abelian₂ := fun j =>
      w0 j - ∑ i, (h (w0 j) (u i) * ((uu i)⁻¹ : Oˣ)) • u i
    have hwu : ∀ j i, h (w j) (u i) = 0 := fun j i => orth_proj h u huo uu huu' (w0 j) i
    have hsw : ∀ l j, h (sv l) (w j) = if l = j then 1 else 0 := by
      intro l j
      have e1 : h (sv l) (w j) = h (sv l) (w0 j) := by
        simp only [w]
        rw [map_sub, orth_pair_gen]
        rw [Finset.sum_eq_zero (fun i _ => by rw [hsu _ (hsvS l) i, mul_zero]), sub_zero]
      rw [e1, ← hw0 j (bS l), Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    have hws : ∀ j l, h (w j) (sv l) = if l = j then 1 else 0 := by
      intro j l
      rw [hH (sv l) (w j), hsw]; split_ifs <;> simp
    let c : Fin r → Module.Free.ChooseBasisIndex O S → O := fun i l => h (t i) (sv l)
    let nn : Fin r → abelian₂ := fun i => t i - ∑ l, c i l • w l
    have hnnsv : ∀ i l, h (nn i) (sv l) = 0 := by
      intro i l
      simp only [nn]
      rw [map_sub, LinearMap.sub_apply, orth_pair_left]
      simp only [hws, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp [c]
    have hnn : ∀ i, nn i ∈ N' := by
      intro i
      refine ⟨fun s hs => ?_, fun i' => ?_⟩
      · have es : s = ∑ l, bS.repr ⟨s, hs⟩ l • sv l := by
          have e0 : ((∑ l, bS.repr ⟨s, hs⟩ l • bS l : S) : abelian₂) = s :=
            congrArg Subtype.val (bS.sum_repr ⟨s, hs⟩)
          rw [Submodule.coe_sum] at e0
          exact e0.symm
        rw [es, orth_pair_gen]
        exact Finset.sum_eq_zero fun l _ => by rw [hnnsv, mul_zero]
      · simp only [nn]
        rw [map_sub, LinearMap.sub_apply, orth_pair_left, htu]
        rw [Finset.sum_eq_zero (fun l _ => by rw [hwu, mul_zero]), sub_zero]
    have hti : ∀ i, t i = ∑ l, c i l • w l + nn i := fun i => by simp [nn]
    have hD : ∀ i l, h (t i) (t l) = (∑ j, c i j * h (w j) (t l) + ∑ j, h (nn i) (w j) * star (c l j))
        + h (nn i) (nn l) := by
      intro i l
      have e1 : h (t i) (t l) = h (∑ j, c i j • w j) (t l) + h (nn i) (t l) := by
        conv_lhs => rw [hti i]
        rw [map_add, LinearMap.add_apply]
      have e2 : h (nn i) (t l) = h (nn i) (∑ j, c l j • w j) + h (nn i) (nn l) := by
        conv_lhs => rw [hti l]
        rw [map_add]
      rw [e1, e2, orth_pair_left, orth_pair_gen, ← add_assoc]
      congr 2
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hdetD : IsUnit (Matrix.of fun i l => h (t i) (t l)).det := by
      have : (Matrix.of fun i l => h (t i) (t l)) = Matrix.diagonal fun i => h (t i) (t i) := by
        ext i l
        rw [Matrix.diagonal_apply, Matrix.of_apply]
        split_ifs with hil
        · rw [hil]
        · exact hto i l hil
      rw [this, Matrix.det_diagonal]
      exact IsUnit.prod_univ_iff.2 htn
    apply not_unit_of_mem_mO hU _ _ hdetD
    rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det]
    let A : Matrix (Fin r) (Module.Free.ChooseBasisIndex O S ⊕ Module.Free.ChooseBasisIndex O S) O :=
      Matrix.of fun i => Sum.elim (fun j => c i j) (fun j => h (nn i) (w j))
    let B : Matrix (Module.Free.ChooseBasisIndex O S ⊕ Module.Free.ChooseBasisIndex O S) (Fin r) O :=
      Matrix.of (Sum.elim (fun j l => h (w j) (t l)) (fun j l => star (c l j)))
    have hmap : (Ideal.Quotient.mk (mO o O)).mapMatrix (Matrix.of fun i l => h (t i) (t l))
        = (A.map (Ideal.Quotient.mk (mO o O))) * (B.map (Ideal.Quotient.mk (mO o O))) := by
      rw [← Matrix.map_mul]
      ext i l
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, A, B,
        Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      rw [hD i l, map_add _ (_ + _), (Ideal.Quotient.eq_zero_iff_mem).2 (hJ _ (hnn i) _ (hnn l)),
        add_zero]
    rw [hmap]
    apply det_mul_eq_zero_of_card_lt
    rw [Fintype.card_sum, Fintype.card_fin, hcardS]
    omega
  refine ⟨Submodule.span O (Set.range t), ?_, hT1, by rw [hT2]; exact hrank, hT3, ?_,
    Submodule.span O (Set.range u), hU1, by rw [hT2, hU2]; omega, ?_, ?_, hU4⟩
  · intro s hs
    obtain ⟨a, b, hab⟩ := hdec s
    have ha : ∀ i, a i = 0 := by
      intro i
      have h1 := hsu s hs i
      rw [hab, map_add, LinearMap.add_apply, orth_pair_left, orth_pair_left,
        Finset.sum_eq_zero (fun j _ => by rw [htu, mul_zero] : ∀ j ∈ univ, b j * h (t j) (u i) = 0),
        add_zero, Finset.sum_eq_single i (fun i' _ hi => by rw [huo i' i hi, mul_zero])
          (fun hi => absurd (Finset.mem_univ _) hi)] at h1
      exact (huu i).mul_left_eq_zero.1 h1
    rw [hab]
    simp only [ha, zero_smul, Finset.sum_const_zero, zero_add]
    exact hmemT b
  · intro x hx hx0
    obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
    have hb : ∀ j, b j = 0 := by
      intro j
      have h1 := hx0 (t j) (Submodule.subset_span ⟨j, rfl⟩)
      rw [orth_pair_left, Finset.sum_eq_single j (fun i' _ hi => by rw [hto i' j hi, mul_zero])
          (fun hi => absurd (Finset.mem_univ _) hi)] at h1
      exact (htn j).mul_left_eq_zero.1 h1
    simp [hb]
  · intro x hx y hy
    obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hy
    rw [orth_pair_left]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [orth_pair_gen, Finset.sum_eq_zero (fun i _ => by rw [htu, mul_zero]), mul_zero]
  · intro x
    obtain ⟨a, b, hab⟩ := hdec x
    exact ⟨_, hmemT b, _, hmemU a, by rw [hab, add_comm]⟩

section annih
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]

def piO (O : Type) [CommRing O] {o : Type} [CommRing o] [Algebra o O] (ϖ : o) (M : ℕ) : AddSubgroup O where
  carrier := {y | ∃ z, y = algebraMap o O (ϖ ^ M) * z}
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by ring⟩
  zero_mem' := ⟨0, by ring⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩; exact ⟨-a, by ring⟩

/- English proof (translation)
Use `hU.free` as an intermediate fact. Establish `: Module.Finite o O` using `Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)`. Set `b` to `Module.Free.chooseBasis o O`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex o O) = 2`. Rewrite using `[← hU.rank2, Module.finrank_eq_card_chooseBasisIndex]`.

Set `NM : AddSubgroup o` to `(Ideal.span {ϖ ^ M}).toAddSubgroup`. Set `f : O →+ (Module.Free.ChooseBasisIndex o O → o ⧸ NM)` to `{ toFun := fun y i => QuotientAddGroup.mk (b.repr y i) map_zero' := by funext i; simp map_add' := fun x y => by funext i; simp }`. Establish `hf : Function.Surjective f`. Introduce `g`. Use `choose r hr using fun i => QuotientAddGroup.mk_surjective (g i)`.

Use `⟨∑ i, r i • b i, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `QuotientAddGroup.mk (b.repr (∑ i, r i • b i) i) = g i`. Rewrite using `[← hr i]`. Use `congr 1`.

Simplify using `[map_sum, Finsupp.finsetSum_apply, Finsupp.single_apply]`. Establish `hker : f.ker = piO O ϖ M`. Use extensionality with `y`. Rewrite using `[AddMonoidHom.mem_ker]`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Establish `h1 : ∀ i, ∃ c, b.repr y i = ϖ ^ M * c`. Introduce `i`. Use `congrFun hy i` as an intermediate fact. Express the relevant statement in the definitionally equal form `QuotientAddGroup.mk (b.repr y i) = (0 : o ⧸ NM) at this`.

Rewrite `this` using `[QuotientAddGroup.eq_zero_iff]`. Conclude with `Ideal.mem_span_singleton.1 this`. Use `choose c hc using h1`. Use `⟨∑ i, c i • b i, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← b.sum_repr y]`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hc i, mul_smul, Algebra.smul_def]`. Introduce and unpack `⟨z, rfl⟩`. Use function extensionality and compare the values at `i`.

Express the relevant statement in the definitionally equal form `QuotientAddGroup.mk (b.repr (algebraMap o O (ϖ ^ M) * z) i) = (0 : o ⧸ NM)`. Rewrite using `[QuotientAddGroup.eq_zero_iff, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `Ideal.mem_span_singleton.2 (dvd_mul_right _ _)`. Establish `hN : Nat.card (o ⧸ NM) = q ^ M` using `index_span_pow ϖ hϖ q hq M`. Rewrite using `[← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf, AddSubgroup.card_top, Nat.card_fun, hN, Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm]`.
-/
lemma index_piO (hU : Unram o O) (ϖ : o) (hϖ : Irreducible ϖ) (q : ℕ)
    (hq : Nat.card (IsLocalRing.ResidueField o) = q) (M : ℕ) : (piO O ϖ M).index = q ^ (2 * M) := by
  classical
  have := hU.free
  have : Module.Finite o O := Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)
  let b := Module.Free.chooseBasis o O
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex o O) = 2 := by
    rw [← hU.rank2, Module.finrank_eq_card_chooseBasisIndex]
  let NM : AddSubgroup o := (Ideal.span {ϖ ^ M}).toAddSubgroup
  let f : O →+ (Module.Free.ChooseBasisIndex o O → o ⧸ NM) :=
    { toFun := fun y i => QuotientAddGroup.mk (b.repr y i)
      map_zero' := by funext i; simp
      map_add' := fun x y => by funext i; simp }
  have hf : Function.Surjective f := by
    intro g
    choose r hr using fun i => QuotientAddGroup.mk_surjective (g i)
    refine ⟨∑ i, r i • b i, ?_⟩
    funext i
    change QuotientAddGroup.mk (b.repr (∑ i, r i • b i) i) = g i
    rw [← hr i]
    congr 1
    simp [map_sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hker : f.ker = piO O ϖ M := by
    ext y
    rw [AddMonoidHom.mem_ker]
    constructor
    · intro hy
      have h1 : ∀ i, ∃ c, b.repr y i = ϖ ^ M * c := by
        intro i
        have := congrFun hy i
        change QuotientAddGroup.mk (b.repr y i) = (0 : o ⧸ NM) at this
        rw [QuotientAddGroup.eq_zero_iff] at this
        exact Ideal.mem_span_singleton.1 this
      choose c hc using h1
      refine ⟨∑ i, c i • b i, ?_⟩
      conv_lhs => rw [← b.sum_repr y]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc i, mul_smul, Algebra.smul_def]
    · rintro ⟨z, rfl⟩
      funext i
      change QuotientAddGroup.mk (b.repr (algebraMap o O (ϖ ^ M) * z) i) = (0 : o ⧸ NM)
      rw [QuotientAddGroup.eq_zero_iff, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
  have hN : Nat.card (o ⧸ NM) = q ^ M := index_span_pow ϖ hϖ q hq M
  rw [← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top, Nat.card_fun, hN, Nat.card_eq_fintype_card, hcard, ← pow_mul,
    mul_comm]

end annih

/- English proof (translation)
Introduce `o O S _ _ _ _ _ _ _ ϖ pr τ ψ q N i hU hϖ hq hq2 hpr hker hiN hτ hψ`. Take `⟨T, hT⟩` from `unram_trace hU`. Establish `hψT : ∀ y, ψ (pr y) = τ (T y)` using `fun y => hψ y (T y) (hT y)`. Establish `hTsm : ∀ (c : o) (y : O), T (algebraMap o O c * y) = c * T y` using `fun c y => by`. Rewrite using `[← Algebra.smul_def, map_smul, smul_eq_mul]`.

Establish `hϖ0 : ϖ ≠ 0` using `hϖ.ne_zero`. Establish `hinj` using `unram_inj hU`. Use `hU.free` as an intermediate fact. Establish `: Module.Finite o O` using `Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)`. Establish `hcancel : ∀ (k : ℕ) (x y : O), algebraMap o O (ϖ ^ k) * x = algebraMap o O (ϖ ^ k) * y → x = y`.

Introduce `k x y hxy`. Rewrite `hxy` using `[← Algebra.smul_def, ← Algebra.smul_def]`. Conclude with `smul_right_injective O (pow_ne_zero k hϖ0) hxy`. Prove the components needed by the constructor for the conclusion. Establish `h1 : pr.toAddMonoidHom.ker = piO O ϖ N`.

Use extensionality with `y`. Rewrite using `[AddMonoidHom.mem_ker]`. Conclude with `hker y`. Rewrite using `[← index_piO hU ϖ hϖ q hq N, ← h1, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hpr]`. Conclude with `(Nat.card_congr (Equiv.Set.univ S)).symm`.

Set `g : O →+ S` to `pr.toAddMonoidHom.comp (AddMonoidHom.mulLeft (algebraMap o O (ϖ ^ i)))`. Establish `hg : ∀ y, g y = pr (algebraMap o O (ϖ ^ i) * y)` using `fun y => rfl`. Establish `hgker : g.ker = piO O ϖ (N - i)`. Use extensionality with `y`. Rewrite using `[AddMonoidHom.mem_ker, hg, hker]`.

Establish `e : ϖ ^ N = ϖ ^ i * ϖ ^ (N - i)` using `by rw [← pow_add]; congr 1; omega`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`. Use `⟨z, hcancel i _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[hz, e, map_mul, mul_assoc]`.

Introduce and unpack `⟨z, rfl⟩`. Conclude with `⟨z, by rw [e, map_mul, mul_assoc]⟩`. Establish `hrange : ∀ y : S, (∀ c, ψ (c * y) = 1) ↔ y ∈ g.range`. Introduce `y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Take `⟨Y0, rfl⟩` from `hpr y`. Establish `h1 : ∀ c' : O, ∃ d, T (c' * Y0) = ϖ ^ i * d`. Introduce `c'`. Distinguish the cases in `ht : T (c' * Y0) = 0`.

Conclude with `⟨0, by rw [ht, mul_zero]⟩`. Take `⟨k, w, hw⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht hϖ`. Establish `h3 : ∀ x, τ (ϖ ^ k * x) = 1`. Introduce `x`. Establish `h4` using `hy (pr (algebraMap o O (((w⁻¹ : oˣ) : o) * x) * c'))`.

Rewrite `h4` using `[← map_mul, hψT, mul_assoc, hTsm, hw]`. Rewrite using `[← h4]`. Use `congr 1`. Establish `: ((w⁻¹ : oˣ) : o) * (w : o) = 1` using `Units.inv_mul w`. Take the linear combination `(-(x * ϖ ^ k)) * this`.

Establish `hik` using `(hτ k).2 h3`. Use `⟨(w : o) * ϖ ^ (k - i), ?_⟩` and prove the remaining obligations. Rewrite using `[hw]`. Establish `e : ϖ ^ k = ϖ ^ i * ϖ ^ (k - i)` using `by rw [← pow_add]; congr 1; omega`. Rewrite using `[e]`.

Expand and normalize the polynomial expressions, which then agree. Set `b` to `Module.Free.chooseBasis o O`. Establish `h5 : ∀ j, ∃ d, b.repr Y0 j = ϖ ^ i * d`. Introduce `j`. Take `⟨bj, hbj⟩` from `hU.tr_perfect (b.coord j)`.

Establish `h6` using `hbj Y0`. Rewrite `h6` using `[mul_comm Y0 (star bj), ← hT, Module.Basis.coord_apply]`. Rewrite using `[hinj h6]`. Conclude with `h1 _`. Use `choose d hd using h5`.

Use `⟨∑ j, d j • b j, ?_⟩` and prove the remaining obligations. Rewrite using `[hg]`. Use `congr 1`. Use `conv_rhs => rw [← b.sum_repr Y0]`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hd j, mul_smul, ← Algebra.smul_def]`. Introduce and unpack `⟨z, rfl⟩ c`. Take `⟨c', rfl⟩` from `hpr c`. Rewrite using `[hg, ← map_mul, hψT, mul_left_comm, hTsm]`.

Conclude with `(hτ i).1 le_rfl _`. Establish `hcard : Nat.card {y : S // ∀ c, ψ (c * y) = 1} = Nat.card g.range` using `Nat.card_congr (Equiv.subtypeEquivRight hrange)`. Rewrite using `[hcard, ← AddSubgroup.index_ker, hgker, index_piO hU ϖ hϖ q hq]`.
-/
theorem annihilator_size : AnnihSize := by
  intro o O S _ _ _ _ _ _ _ ϖ pr τ ψ q N i hU hϖ hq hq2 hpr hker hiN hτ hψ
  classical
  obtain ⟨T, hT⟩ := unram_trace hU
  have hψT : ∀ y, ψ (pr y) = τ (T y) := fun y => hψ y (T y) (hT y)
  have hTsm : ∀ (c : o) (y : O), T (algebraMap o O c * y) = c * T y := fun c y => by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hinj := unram_inj hU
  have := hU.free
  have : Module.Finite o O := Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)
  have hcancel : ∀ (k : ℕ) (x y : O), algebraMap o O (ϖ ^ k) * x = algebraMap o O (ϖ ^ k) * y → x = y := by
    intro k x y hxy
    rw [← Algebra.smul_def, ← Algebra.smul_def] at hxy
    exact smul_right_injective O (pow_ne_zero k hϖ0) hxy
  constructor
  · have h1 : pr.toAddMonoidHom.ker = piO O ϖ N := by
      ext y
      rw [AddMonoidHom.mem_ker]
      exact hker y
    rw [← index_piO hU ϖ hϖ q hq N, ← h1, AddSubgroup.index_ker,
      AddMonoidHom.range_eq_top.2 hpr]
    exact (Nat.card_congr (Equiv.Set.univ S)).symm
  · let g : O →+ S := pr.toAddMonoidHom.comp (AddMonoidHom.mulLeft (algebraMap o O (ϖ ^ i)))
    have hg : ∀ y, g y = pr (algebraMap o O (ϖ ^ i) * y) := fun y => rfl
    have hgker : g.ker = piO O ϖ (N - i) := by
      ext y
      rw [AddMonoidHom.mem_ker, hg, hker]
      have e : ϖ ^ N = ϖ ^ i * ϖ ^ (N - i) := by rw [← pow_add]; congr 1; omega
      constructor
      · rintro ⟨z, hz⟩
        refine ⟨z, hcancel i _ _ ?_⟩
        rw [hz, e, map_mul, mul_assoc]
      · rintro ⟨z, rfl⟩
        exact ⟨z, by rw [e, map_mul, mul_assoc]⟩
    have hrange : ∀ y : S, (∀ c, ψ (c * y) = 1) ↔ y ∈ g.range := by
      intro y
      constructor
      · intro hy
        obtain ⟨Y0, rfl⟩ := hpr y
        have h1 : ∀ c' : O, ∃ d, T (c' * Y0) = ϖ ^ i * d := by
          intro c'
          by_cases ht : T (c' * Y0) = 0
          · exact ⟨0, by rw [ht, mul_zero]⟩
          · obtain ⟨k, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht hϖ
            have h3 : ∀ x, τ (ϖ ^ k * x) = 1 := by
              intro x
              have h4 := hy (pr (algebraMap o O (((w⁻¹ : oˣ) : o) * x) * c'))
              rw [← map_mul, hψT, mul_assoc, hTsm, hw] at h4
              rw [← h4]
              congr 1
              have : ((w⁻¹ : oˣ) : o) * (w : o) = 1 := Units.inv_mul w
              linear_combination (-(x * ϖ ^ k)) * this
            have hik := (hτ k).2 h3
            refine ⟨(w : o) * ϖ ^ (k - i), ?_⟩
            rw [hw]
            have e : ϖ ^ k = ϖ ^ i * ϖ ^ (k - i) := by rw [← pow_add]; congr 1; omega
            rw [e]; ring
        let b := Module.Free.chooseBasis o O
        have h5 : ∀ j, ∃ d, b.repr Y0 j = ϖ ^ i * d := by
          intro j
          obtain ⟨bj, hbj⟩ := hU.tr_perfect (b.coord j)
          have h6 := hbj Y0
          rw [mul_comm Y0 (star bj), ← hT, Module.Basis.coord_apply] at h6
          rw [hinj h6]
          exact h1 _
        choose d hd using h5
        refine ⟨∑ j, d j • b j, ?_⟩
        rw [hg]
        congr 1
        conv_rhs => rw [← b.sum_repr Y0]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hd j, mul_smul, ← Algebra.smul_def]
      · rintro ⟨z, rfl⟩ c
        obtain ⟨c', rfl⟩ := hpr c
        rw [hg, ← map_mul, hψT, mul_left_comm, hTsm]
        exact (hτ i).1 le_rfl _
    have hcard : Nat.card {y : S // ∀ c, ψ (c * y) = 1} = Nat.card g.range :=
      Nat.card_congr (Equiv.subtypeEquivRight hrange)
    rw [hcard, ← AddSubgroup.index_ker, hgker, index_piO hU ϖ hϖ q hq]

/- English proof (translation)
The claim follows from `Part2.hermGaussCond hermitian_gauss_sum_ring annihilator_size`.
-/
theorem hermitian_gauss_condition : HermGaussCond := Part2.hermGaussCond hermitian_gauss_sum_ring annihilator_size

section stdform
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

/- English proof (translation)
Establish `hq1 : 1 < Fintype.card K` using `Fintype.one_lt_card`. Take `⟨g, hg⟩` from `IsCyclic.exists_generator (α := Lˣ)`. Take `⟨k, hk⟩ : ∃ k : ℕ, g ^ k = Units.mk0 a ha0` from `Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 (hg _))`. Establish `hord : orderOf g = (Fintype.card K + 1) * (Fintype.card K - 1)`. Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units, card_L h2]`.

Take `⟨c, hc⟩ : ∃ c, Fintype.card K = c + 1` from `⟨Fintype.card K - 1, by omega⟩`. Rewrite using `[hc]`. Simplify using `only [Nat.add_sub_cancel]`. Establish `: (c + 1) ^ 2 = (c + 1 + 1) * c + 1` using `by ring`. Use linear arithmetic over natural numbers and integers.

Establish `h1 : (Units.mk0 a ha0) ^ (Fintype.card K - 1) = 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]`. Establish `: a ^ (Fintype.card K - 1) * a = 1 * a`. Rewrite using `[← pow_succ, one_mul]`.

Establish `: Fintype.card K - 1 + 1 = Fintype.card K` using `by omega`. Rewrite using `[this, ha]`. Conclude with `mul_right_cancel₀ ha0 this`. Rewrite `h1` using `[← hk, ← pow_mul]`. Establish `h3` using `orderOf_dvd_of_pow_eq_one h1`.

Rewrite `h3` using `[hord]`. Establish `h4 : (Fintype.card K + 1) ∣ k` using `Nat.dvd_of_mul_dvd_mul_right (by omega) h3`. Take `⟨k', rfl⟩` from `h4`. Use `⟨((g ^ k' : Lˣ) : L), ?_⟩` and prove the remaining obligations. Use `congrArg Units.val hk` as an intermediate fact.

Rewrite `this` using `[Units.val_mk0]`. Rewrite using `[← this, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm]`.
-/
lemma norm_surj (h2 : Module.finrank K L = 2) (a : L) (ha0 : a ≠ 0)
    (ha : a ^ Fintype.card K = a) : ∃ lam : L, lam ^ (Fintype.card K + 1) = a := by
  classical
  have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Lˣ)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, g ^ k = Units.mk0 a ha0 :=
    Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 (hg _))
  have hord : orderOf g = (Fintype.card K + 1) * (Fintype.card K - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units,
      card_L h2]
    obtain ⟨c, hc⟩ : ∃ c, Fintype.card K = c + 1 := ⟨Fintype.card K - 1, by omega⟩
    rw [hc]
    simp only [Nat.add_sub_cancel]
    have : (c + 1) ^ 2 = (c + 1 + 1) * c + 1 := by ring
    omega
  have h1 : (Units.mk0 a ha0) ^ (Fintype.card K - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    have : a ^ (Fintype.card K - 1) * a = 1 * a := by
      rw [← pow_succ, one_mul]
      have : Fintype.card K - 1 + 1 = Fintype.card K := by omega
      rw [this, ha]
    exact mul_right_cancel₀ ha0 this
  rw [← hk, ← pow_mul] at h1
  have h3 := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at h3
  have h4 : (Fintype.card K + 1) ∣ k := Nat.dvd_of_mul_dvd_mul_right (by omega) h3
  obtain ⟨k', rfl⟩ := h4
  refine ⟨((g ^ k' : Lˣ) : L), ?_⟩
  have := congrArg Units.val hk
  rw [Units.val_mk0] at this
  rw [← this, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm]

variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)

/- English proof (translation)
Simplify using `only [hB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]`.
-/
lemma hB_smul_left (c : L) (x y : Fin n → L) : hB K Ph (c • x) y = c * hB K Ph x y := by
  simp only [hB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [hB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_pow]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring`.
-/
lemma hB_smul_right (c : L) (x y : Fin n → L) :
    hB K Ph x (c • y) = c ^ Fintype.card K * hB K Ph x y := by
  simp only [hB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_pow]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

end stdform

/- English proof (translation)
Introduce `K L _ _ _ _ _ h2 n Ph hPh hherm`. Set `_ : StarRing L` to `frobStar h2`. Set `h : (Fin n → L) →ₗ[L] (Fin n → L) →ₗ⋆[L] L` to `LinearMap.mk₂'ₛₗ (RingHom.id L) (starRingEnd L) (fun x y => hB K Ph x y) (hB_add_left Ph) (fun c x y => hB_smul_left Ph c x y) (hB_add_right Ph) (fun c x y => hB_smul_right Ph c x y)`. Establish `hh : ∀ x y, h x y = hB K Ph x y` using `fun x y => rfl`. Establish `hH : IsHerm h` using `fun v w => (hB_conj Ph h2 hherm v w).symm`.

Establish `hSD : SelfDual h`. Use `⟨hH, fun φ => ?_⟩` and prove the remaining obligations. Set `f : Fin n → L` to `fun k => φ (fun j => if k = j then 1 else 0)`. Use `⟨fun l => (Ph⁻¹.mulVec f l) ^ Fintype.card K, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[hh, LinearMap.pi_apply_eq_sum_univ φ v]`.

Simplify using `only [hB, frob_frob h2]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `e1 : ∑ l, Ph k l * Ph⁻¹.mulVec f l = f k`. Establish `: Ph.mulVec (Ph⁻¹.mulVec f) = f`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Ph hPh, Matrix.one_mulVec]`.

Conclude with `congrFun this k`. Rewrite using `[smul_eq_mul]`. Express the relevant statement in the definitionally equal form `v k * f k = _`. Rewrite using `[← e1, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`.

Take `⟨θ, hθ⟩` from `trace_surj (K := K) (L := L) 1`. Establish `hθ' : θ + θ ^ Fintype.card K = 1` using `by rw [← trace_eq h2, hθ, map_one]`. Establish `hpol : ∀ C : Submodule L (Fin n → L), (∀ c ∈ C, ¬ IsUnit (h c c)) → ∀ c ∈ C, ∀ c' ∈ C, h c c' ∈ (⊥ : Ideal L)`. Introduce `C hC c hc c' hc'`. Establish `h0 : ∀ x ∈ C, hB K Ph x x = 0` using `fun x hx => by`.

Assume the negation of the conclusion as `hne`. Conclude with `hC x hx (isUnit_iff_ne_zero.2 hne)`. Rewrite using `[Ideal.mem_bot, hh]`. Assume the negation of the conclusion as `hz`. Establish `e1` using `h0 _ (C.add_mem (C.smul_mem (θ / hB K Ph c c') hc) hc')`.

Rewrite `e1` using `[hB_add_left, hB_add_right, hB_add_right, h0 _ (C.smul_mem _ hc), h0 _ hc', ← hB_conj Ph h2 hherm ((θ / hB K Ph c c') • c) c', hB_smul_left, div_mul_cancel₀ _ hz]`. Rewrite `e1` using `[zero_add, add_zero, hθ']`. Conclude with `one_ne_zero e1`. Take `⟨v, horth, hunit⟩` from `exists_orth_family_gen h ⊥ (fun x hx => by rw [Ideal.mem_bot] at hx; rw [hx]; exact not_isUnit_zero) hpol hSD n (by rw [Module.finrank_fin_fun])`. Establish `hlam : ∀ i, ∃ lam : L, lam ^ (Fintype.card K + 1) = (hB K Ph (v i) (v i))⁻¹`.

Introduce `i`. Establish `hne : hB K Ph (v i) (v i) ≠ 0` using `(hunit i).ne_zero`. Conclude with `norm_surj h2 _ (inv_ne_zero hne) (by rw [inv_pow, hB_conj Ph h2 hherm])`. Use `choose lam hlam using hlam`. Set `A : Matrix (Fin n) (Fin n) L` to `Matrix.of fun i k => lam i * v i k`.

Establish `hA : A * Ph * (A.map fun y => y ^ Fintype.card K).transpose = 1`. Use extensionality with `i i'`. Establish `e1 : (A * Ph * (A.map fun y => y ^ Fintype.card K).transpose) i i' = hB K Ph (lam i • v i) (lam i' • v i')`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, A, Matrix.of_apply, hB, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.

Rewrite using `[e1, hB_smul_left, hB_smul_right, Matrix.one_apply]`. Use `split_ifs with hii`. Substitute `hii` using the available equality. Establish `hne : hB K Ph (v i) (v i) ≠ 0` using `(hunit i).ne_zero`. Rewrite using `[← mul_assoc, ← pow_succ', hlam, inv_mul_cancel₀ hne]`.

Establish `: hB K Ph (v i) (v i') = 0` using `horth i i' hii`. Rewrite using `[this, mul_zero, mul_zero]`. Use `⟨A, ?_, hA⟩` and prove the remaining obligations. Use `congrArg Matrix.det hA` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_one, mul_assoc]`.

Conclude with `IsUnit.of_mul_eq_one _ this`.
-/
theorem hermitian_standard_form : HermStdForm := by
  intro K L _ _ _ _ _ h2 n Ph hPh hherm
  classical
  let _ : StarRing L := frobStar h2
  let h : (Fin n → L) →ₗ[L] (Fin n → L) →ₗ⋆[L] L :=
    LinearMap.mk₂'ₛₗ (RingHom.id L) (starRingEnd L) (fun x y => hB K Ph x y)
      (hB_add_left Ph) (fun c x y => hB_smul_left Ph c x y) (hB_add_right Ph)
      (fun c x y => hB_smul_right Ph c x y)
  have hh : ∀ x y, h x y = hB K Ph x y := fun x y => rfl
  have hH : IsHerm h := fun v w => (hB_conj Ph h2 hherm v w).symm
  have hSD : SelfDual h := by
    refine ⟨hH, fun φ => ?_⟩
    let f : Fin n → L := fun k => φ (fun j => if k = j then 1 else 0)
    refine ⟨fun l => (Ph⁻¹.mulVec f l) ^ Fintype.card K, fun v => ?_⟩
    rw [hh, LinearMap.pi_apply_eq_sum_univ φ v]
    simp only [hB, frob_frob h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : ∑ l, Ph k l * Ph⁻¹.mulVec f l = f k := by
      have : Ph.mulVec (Ph⁻¹.mulVec f) = f := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Ph hPh, Matrix.one_mulVec]
      exact congrFun this k
    rw [smul_eq_mul]
    change v k * f k = _
    rw [← e1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  obtain ⟨θ, hθ⟩ := trace_surj (K := K) (L := L) 1
  have hθ' : θ + θ ^ Fintype.card K = 1 := by rw [← trace_eq h2, hθ, map_one]
  have hpol : ∀ C : Submodule L (Fin n → L), (∀ c ∈ C, ¬ IsUnit (h c c)) →
      ∀ c ∈ C, ∀ c' ∈ C, h c c' ∈ (⊥ : Ideal L) := by
    intro C hC c hc c' hc'
    have h0 : ∀ x ∈ C, hB K Ph x x = 0 := fun x hx => by
      by_contra hne
      exact hC x hx (isUnit_iff_ne_zero.2 hne)
    rw [Ideal.mem_bot, hh]
    by_contra hz
    have e1 := h0 _ (C.add_mem (C.smul_mem (θ / hB K Ph c c') hc) hc')
    rw [hB_add_left, hB_add_right, hB_add_right, h0 _ (C.smul_mem _ hc), h0 _ hc',
      ← hB_conj Ph h2 hherm ((θ / hB K Ph c c') • c) c', hB_smul_left, div_mul_cancel₀ _ hz] at e1
    rw [zero_add, add_zero, hθ'] at e1
    exact one_ne_zero e1
  obtain ⟨v, horth, hunit⟩ := exists_orth_family_gen h ⊥
    (fun x hx => by rw [Ideal.mem_bot] at hx; rw [hx]; exact not_isUnit_zero) hpol hSD n
    (by rw [Module.finrank_fin_fun])
  have hlam : ∀ i, ∃ lam : L, lam ^ (Fintype.card K + 1) = (hB K Ph (v i) (v i))⁻¹ := by
    intro i
    have hne : hB K Ph (v i) (v i) ≠ 0 := (hunit i).ne_zero
    exact norm_surj h2 _ (inv_ne_zero hne) (by rw [inv_pow, hB_conj Ph h2 hherm])
  choose lam hlam using hlam
  let A : Matrix (Fin n) (Fin n) L := Matrix.of fun i k => lam i * v i k
  have hA : A * Ph * (A.map fun y => y ^ Fintype.card K).transpose = 1 := by
    ext i i'
    have e1 : (A * Ph * (A.map fun y => y ^ Fintype.card K).transpose) i i'
        = hB K Ph (lam i • v i) (lam i' • v i') := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, A, Matrix.of_apply, hB,
        Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      exact Finset.sum_comm
    rw [e1, hB_smul_left, hB_smul_right, Matrix.one_apply]
    split_ifs with hii
    · subst hii
      have hne : hB K Ph (v i) (v i) ≠ 0 := (hunit i).ne_zero
      rw [← mul_assoc, ← pow_succ', hlam, inv_mul_cancel₀ hne]
    · have : hB K Ph (v i) (v i') = 0 := horth i i' hii
      rw [this, mul_zero, mul_zero]
  refine ⟨A, ?_, hA⟩
  have := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one, mul_assoc] at this
  exact IsUnit.of_mul_eq_one _ this

section hermjac
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]

omit [StarRing E] in
/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `finrank_le_one (R := F) (1 : E) (fun w => by` as an intermediate fact. Take `⟨c, hc⟩` from `hcon w`. Conclude with `⟨c, by rw [Algebra.smul_def, mul_one, hc]⟩)`.

Use linear arithmetic over natural numbers and integers.
-/
lemma hj_exists_omega (h2 : Module.finrank F E = 2) : ∃ ω : E, ∀ c : F, algebraMap F E c ≠ ω := by
  by_contra hcon
  push Not at hcon
  have := finrank_le_one (R := F) (1 : E) (fun w => by
    obtain ⟨c, hc⟩ := hcon w
    exact ⟨c, by rw [Algebra.smul_def, mul_one, hc]⟩)
  omega

omit [StarRing E] in
/- English proof (translation)
Establish `: Nontrivial E` using `Module.nontrivial_of_finrank_pos (R := F) (by rw [h2]; norm_num)`. Establish `hli : LinearIndependent F ![(1 : E), ω]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Establish `ht : t = 0`.

Assume the negation of the conclusion as `ht`. Apply `hω (-s / t)` to reduce the goal to its premises. Establish `h1 : algebraMap F E t * ω = - algebraMap F E s`. Rewrite `hst` using `[Algebra.smul_def, Algebra.smul_def, mul_one]`. Take the linear combination `hst`.

Establish `h3 : algebraMap F E t * algebraMap F E t⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel₀ ht, map_one]`. Rewrite using `[div_eq_mul_inv, map_mul, map_neg]`. Take the linear combination `(-(algebraMap F E t⁻¹)) * h1 + ω * h3`. Use `⟨?_, ht⟩` and prove the remaining obligations.

Rewrite `hst` using `[ht, zero_smul, add_zero, Algebra.smul_def, mul_one]`. Conclude with `(map_eq_zero_iff _ (algebraMap F E).injective).1 hst`. Apply the tactic sequence `refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [h2]; rfl), ?_, ?_⟩ <;> simp`.
-/
lemma hj_basis (h2 : Module.finrank F E = 2) (ω : E) (hω : ∀ c : F, algebraMap F E c ≠ ω) :
    ∃ β : Module.Basis (Fin 2) F E, β 0 = 1 ∧ β 1 = ω := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [h2]; norm_num)
  have hli : LinearIndependent F ![(1 : E), ω] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hω (-s / t)
      have h1 : algebraMap F E t * ω = - algebraMap F E s := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        linear_combination hst
      have h3 : algebraMap F E t * algebraMap F E t⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ ht, map_one]
      rw [div_eq_mul_inv, map_mul, map_neg]
      linear_combination (-(algebraMap F E t⁻¹)) * h1 + ω * h3
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
    exact (map_eq_zero_iff _ (algebraMap F E).injective).1 hst
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [h2]; rfl), ?_, ?_⟩ <;> simp

omit [StarRing E] in
/- English proof (translation)
Establish `: algebraMap F E c0 + algebraMap F E c1 * ω = c0 • β 0 + c1 • β 1`. Rewrite using `[h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]`. Rewrite using `[this]`. Apply the tactic sequence `constructor <;> simp`.
-/
lemma hj_repr (β : Module.Basis (Fin 2) F E) (ω : E) (h0 : β 0 = 1) (h1 : β 1 = ω) (c0 c1 : F) :
    β.repr (algebraMap F E c0 + algebraMap F E c1 * ω) 0 = c0 ∧
    β.repr (algebraMap F E c0 + algebraMap F E c1 * ω) 1 = c1 := by
  have : algebraMap F E c0 + algebraMap F E c1 * ω = c0 • β 0 + c1 • β 1 := by
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]
  rw [this]
  constructor <;> simp

omit [StarRing E] in
/- English proof (translation)
Use `conv_lhs => rw [← β.sum_repr e, Fin.sum_univ_two, h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]`.
-/
lemma hj_decomp (β : Module.Basis (Fin 2) F E) (ω : E) (h0 : β 0 = 1) (h1 : β 1 = ω) (e : E) :
    e = algebraMap F E (β.repr e 0) + algebraMap F E (β.repr e 1) * ω := by
  conv_lhs => rw [← β.sum_repr e, Fin.sum_univ_two, h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]

omit [StarRing E] in
/- English proof (translation)
Rewrite using `[Algebra.norm_eq_matrix_det β, Matrix.det_fin_two]`. Simplify using `only [Algebra.leftMulMatrix_eq_repr_mul, h0, h1, mul_one]`. Establish `e1 : (algebraMap F E a + algebraMap F E b * ω) * ω = algebraMap F E (-(b * nn)) + algebraMap F E (a + b * t) * ω`. Simplify using `only [map_neg, map_mul, map_add]`. Take the linear combination `(algebraMap F E b) * hω2`.

Rewrite using `[e1, (hj_repr β ω h0 h1 _ _).1, (hj_repr β ω h0 h1 _ _).2, (hj_repr β ω h0 h1 _ _).1, (hj_repr β ω h0 h1 _ _).2]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hj_norm (β : Module.Basis (Fin 2) F E) (ω : E) (h0 : β 0 = 1) (h1 : β 1 = ω) (t nn : F)
    (hω2 : ω * ω = algebraMap F E t * ω - algebraMap F E nn) (a b : F) :
    Algebra.norm F (algebraMap F E a + algebraMap F E b * ω) = a ^ 2 + a * b * t + b ^ 2 * nn := by
  rw [Algebra.norm_eq_matrix_det β, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, h0, h1, mul_one]
  have e1 : (algebraMap F E a + algebraMap F E b * ω) * ω
      = algebraMap F E (-(b * nn)) + algebraMap F E (a + b * t) * ω := by
    simp only [map_neg, map_mul, map_add]
    linear_combination (algebraMap F E b) * hω2
  rw [e1, (hj_repr β ω h0 h1 _ _).1, (hj_repr β ω h0 h1 _ _).2, (hj_repr β ω h0 h1 _ _).1,
    (hj_repr β ω h0 h1 _ _).2]
  ring

/- English proof (translation)
Take `⟨ω, hω⟩` from `hj_exists_omega (F := F) (E := E) h2`. Take `⟨β, h0, h1⟩` from `hj_basis h2 ω hω`. Take `⟨t, ht⟩` from `hfix (ω + star ω) (by rw [star_add, star_star, add_comm])`. Take `⟨nn, hnn⟩` from `hfix (ω * star ω) (by rw [star_mul', star_star, mul_comm])`. Establish `hst : star ω = algebraMap F E t - ω` using `by rw [ht]; ring`.

Establish `hω2 : ω * ω = algebraMap F E t * ω - algebraMap F E nn`. Rewrite using `[hnn, hst]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hj_decomp β ω h0 h1 x, hj_norm β ω h0 h1 t nn hω2]`. Simplify using `only [star_add, star_mul', hs, hst, map_add, map_mul, map_pow]`.

Take the linear combination `((algebraMap F E (β.repr x 1)) ^ 2) * hω2`.
-/
lemma hj_norm_star (hs : ∀ c : F, star (algebraMap F E c) = algebraMap F E c)
    (h2 : Module.finrank F E = 2) (hfix : ∀ y : E, star y = y → ∃ c : F, algebraMap F E c = y)
    (x : E) : algebraMap F E (Algebra.norm F x) = x * star x := by
  obtain ⟨ω, hω⟩ := hj_exists_omega (F := F) (E := E) h2
  obtain ⟨β, h0, h1⟩ := hj_basis h2 ω hω
  obtain ⟨t, ht⟩ := hfix (ω + star ω) (by rw [star_add, star_star, add_comm])
  obtain ⟨nn, hnn⟩ := hfix (ω * star ω) (by rw [star_mul', star_star, mul_comm])
  have hst : star ω = algebraMap F E t - ω := by rw [ht]; ring
  have hω2 : ω * ω = algebraMap F E t * ω - algebraMap F E nn := by
    rw [hnn, hst]; ring
  rw [hj_decomp β ω h0 h1 x, hj_norm β ω h0 h1 t nn hω2]
  simp only [star_add, star_mul', hs, hst, map_add, map_mul, map_pow]
  linear_combination ((algebraMap F E (β.repr x 1)) ^ 2) * hω2

end hermjac

section hermjacA
variable {E : Type} [CommRing E]

def rmulE (m : ℕ) (A : Matrix (Fin m) (Fin m) E) :
    Matrix (Fin m) (Fin m) E →ₗ[E] Matrix (Fin m) (Fin m) E :=
  { toFun := fun X : Matrix (Fin m) (Fin m) E => X * A
    map_add' := fun X Y => Matrix.add_mul X Y A
    map_smul' := fun c X => Matrix.smul_mul c X A }

def lmulE (m : ℕ) (B : Matrix (Fin m) (Fin m) E) :
    Matrix (Fin m) (Fin m) E →ₗ[E] Matrix (Fin m) (Fin m) E :=
  { toFun := fun X : Matrix (Fin m) (Fin m) E => B * X
    map_add' := fun X Y => Matrix.mul_add B X Y
    map_smul' := fun c X => Matrix.mul_smul B c X }

/- English proof (translation)
The claim follows from `tuple_jacobian_alt E m m A`.
-/
lemma det_rmulE (m : ℕ) (A : Matrix (Fin m) (Fin m) E) : LinearMap.det (rmulE m A) = A.det ^ m :=
  tuple_jacobian_alt E m m A

/- English proof (translation)
Establish `h1 : lmulE m B = ((Matrix.transposeLinearEquiv (Fin m) (Fin m) E E : _ ≃ₗ[E] _) : _ →ₗ[E] _) ∘ₗ rmulE m B.transpose ∘ₗ ((Matrix.transposeLinearEquiv (Fin m) (Fin m) E E).symm : _ →ₗ[E] _)`. Use extensionality with `X i j`. Simplify using `only [lmulE, rmulE, Matrix.transposeLinearEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]`. Express the relevant statement in the definitionally equal form `(B * X) i j = (X.transpose * B.transpose).transpose i j`. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]`.

Rewrite using `[h1, LinearMap.det_conj, det_rmulE, Matrix.det_transpose]`.
-/
lemma det_lmulE (m : ℕ) (B : Matrix (Fin m) (Fin m) E) : LinearMap.det (lmulE m B) = B.det ^ m := by
  have h1 : lmulE m B = ((Matrix.transposeLinearEquiv (Fin m) (Fin m) E E : _ ≃ₗ[E] _) : _ →ₗ[E] _) ∘ₗ
      rmulE m B.transpose ∘ₗ
      ((Matrix.transposeLinearEquiv (Fin m) (Fin m) E E).symm : _ →ₗ[E] _) := by
    ext X i j
    simp only [lmulE, rmulE, Matrix.transposeLinearEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    change (B * X) i j = (X.transpose * B.transpose).transpose i j
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
  rw [h1, LinearMap.det_conj, det_rmulE, Matrix.det_transpose]

/- English proof (translation)
Rewrite using `[LinearMap.det_comp, det_rmulE, det_lmulE, Matrix.det_conjTranspose, mul_pow]`.
-/
lemma det_congrE [StarRing E] (m : ℕ) (A : Matrix (Fin m) (Fin m) E) :
    LinearMap.det (rmulE m A ∘ₗ lmulE m A.conjTranspose) = (A.det * star A.det) ^ m := by
  rw [LinearMap.det_comp, det_rmulE, det_lmulE, Matrix.det_conjTranspose, mul_pow]

end hermjacA

section hermjacA2
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]

/- English proof (translation)
Establish `: Nontrivial E` using `Module.nontrivial_of_finrank_pos (R := F) (by rw [h2]; norm_num)`. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [h2]; norm_num)`. Set `b` to `Module.Free.chooseBasis F (hermSub F E hs m)`. Set `v : Module.Free.ChooseBasisIndex F (hermSub F E hs m) → Matrix (Fin m) (Fin m) E` to `fun i => (b i : Matrix (Fin m) (Fin m) E)`. Establish `hcoe : ∀ a : Module.Free.ChooseBasisIndex F (hermSub F E hs m) → F, ((∑ i, a i • b i : hermSub F E hs m) : Matrix (Fin m) (Fin m) E) = ∑ i, algebraMap F E (a i) • v i`.

Introduce `a`. Rewrite using `[Submodule.coe_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [Submodule.coe_smul, algebraMap_smul]`. Establish `hherm : ∀ Y : hermSub F E hs m, (Y : Matrix (Fin m) (Fin m) E).conjTranspose = Y` using `fun Y => Y.2`. Take `⟨u, hu⟩` from `hδ`.

Establish `hli : LinearIndependent E v`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Set `H1 : hermSub F E hs m` to `∑ i, β.repr (g i) 0 • b i`. Set `H2 : hermSub F E hs m` to `∑ i, β.repr (g i) 1 • b i`.

Establish `e1 : (H1 : Matrix (Fin m) (Fin m) E) + ω • (H2 : Matrix (Fin m) (Fin m) E) = 0`. Rewrite using `[← hg, hcoe, hcoe, Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [hj_decomp β ω h0 h1 (g i)]`. Rewrite using `[add_smul, smul_smul, mul_comm ω]`.

Establish `e2 : (H1 : Matrix (Fin m) (Fin m) E) + star ω • (H2 : Matrix (Fin m) (Fin m) E) = 0`. Use `congrArg Matrix.conjTranspose e1` as an intermediate fact. Rewrite `this` using `[Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hherm, hherm, Matrix.conjTranspose_zero]`. Then use the resulting hypothesis. Establish `e3 : (u : E) • (H2 : Matrix (Fin m) (Fin m) E) = 0`. Rewrite using `[hu, sub_smul]`.

Use `congrArg₂ (· - ·) e1 e2` as an intermediate fact. Simplify using `using this`. Establish `e4 : (H2 : Matrix (Fin m) (Fin m) E) = 0`. Use `congrArg (fun X => ((u⁻¹ : Eˣ) : E) • X) e3` as an intermediate fact. Simplify `this` using `[smul_smul]`.

Establish `e5 : (H1 : Matrix (Fin m) (Fin m) E) = 0`. Rewrite `e1` using `[e4, smul_zero, add_zero]`. Conclude with `e1`. Establish `hb` using `Fintype.linearIndependent_iff.1 b.linearIndependent`. Establish `z1` using `hb _ (Subtype.ext e5 : H1 = 0)`.

Establish `z2` using `hb _ (Subtype.ext e4 : H2 = 0)`. Introduce `i`. Rewrite using `[hj_decomp β ω h0 h1 (g i), z1 i, z2 i]`. Simplify using the standard rewrite rules. Establish `hmem : ∀ Y : hermSub F E hs m, (Y : Matrix (Fin m) (Fin m) E) = ∑ i, algebraMap F E (b.repr Y i) • v i`.

Introduce `Y`. Use `conv_lhs => rw [← b.sum_repr Y]`. Conclude with `hcoe _`. Establish `hmem' : ∀ Y : hermSub F E hs m, (Y : Matrix (Fin m) (Fin m) E) ∈ Submodule.span E (Set.range v)`. Introduce `Y`.

Rewrite using `[hmem Y]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hstu : star ((u⁻¹ : Eˣ) : E) = -((u⁻¹ : Eˣ) : E)`. Establish `a1 : (u : E) * ((u⁻¹ : Eˣ) : E) = 1` using `Units.mul_inv u`. Establish `a2 : star (u : E) = -(u : E)` using `by rw [hu, star_sub, star_star]; ring`.

Establish `a3 : star (u : E) * star ((u⁻¹ : Eˣ) : E) = 1` using `by rw [← star_mul', a1, star_one]`. Rewrite `a3` using `[a2]`. Take the linear combination `(-((u⁻¹ : Eˣ) : E)) * a3 - (star ((u⁻¹ : Eˣ) : E)) * a1`. Establish `hsp : ⊤ ≤ Submodule.span E (Set.range v)`. Introduce `X _`.

Set `X2 : Matrix (Fin m) (Fin m) E` to `((u⁻¹ : Eˣ) : E) • (X - X.conjTranspose)`. Establish `hX2 : X2.conjTranspose = X2`. Simplify using `only [X2]`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, hstu, neg_smul, ← smul_neg, neg_sub]`. Establish `hX1 : (X - ω • X2).conjTranspose = X - ω • X2`.

Rewrite using `[Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hX2]`. Establish `a1 : (u : E) • X2 = X - X.conjTranspose`. Simplify using `only [X2]`. Rewrite using `[smul_smul, Units.mul_inv, one_smul]`. Rewrite `a1` using `[hu, sub_smul]`.

Rewrite using `[sub_eq_sub_iff_add_eq_add]`. Use `a1` as an intermediate fact. Rewrite `this` using `[sub_eq_sub_iff_add_eq_add]`. Rewrite using `[add_comm, this, add_comm]`. Establish `: X = (X - ω • X2) + ω • X2` using `by abel`.

Rewrite using `[this]`. Conclude with `Submodule.add_mem _ (hmem' ⟨_, hX1⟩) (Submodule.smul_mem _ _ (hmem' ⟨_, hX2⟩))`. Set `bE` to `Module.Basis.mk hli hsp`. Establish `hbE : ∀ i, bE i = v i` using `fun i => Module.Basis.mk_apply hli hsp i`. Establish `hmat : LinearMap.toMatrix bE bE (rmulE m A ∘ₗ lmulE m A.conjTranspose) = (algebraMap F E).mapMatrix (LinearMap.toMatrix b b (congrHerm F E hs m A))`.

Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]`. Establish `e1 : (rmulE m A ∘ₗ lmulE m A.conjTranspose) (bE j) = ∑ i, algebraMap F E (b.repr (congrHerm F E hs m A (b j)) i) • bE i`. Simplify using `only [hbE]`. Rewrite using `[← hmem]`.

Both sides reduce to the same expression. Rewrite using `[e1, Module.Basis.repr_sum_self]`. Apply `(algebraMap F E).injective` to reduce the goal to its premises. Rewrite using `[map_pow, hj_norm_star hs h2 hfix, ← det_congrE, ← LinearMap.det_toMatrix bE, hmat, ← RingHom.map_det, LinearMap.det_toMatrix]`.
-/
lemma hj_caseA (hs : ∀ c : F, star (algebraMap F E c) = algebraMap F E c)
    (h2 : Module.finrank F E = 2) (hfix : ∀ y : E, star y = y → ∃ c : F, algebraMap F E c = y)
    (ω : E) (β : Module.Basis (Fin 2) F E) (h0 : β 0 = 1) (h1 : β 1 = ω)
    (hδ : IsUnit (ω - star ω)) (m : ℕ) (A : Matrix (Fin m) (Fin m) E) :
    LinearMap.det (congrHerm F E hs m A) = Algebra.norm F A.det ^ m := by
  classical
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [h2]; norm_num)
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  let b := Module.Free.chooseBasis F (hermSub F E hs m)
  let v : Module.Free.ChooseBasisIndex F (hermSub F E hs m) → Matrix (Fin m) (Fin m) E :=
    fun i => (b i : Matrix (Fin m) (Fin m) E)
  have hcoe : ∀ a : Module.Free.ChooseBasisIndex F (hermSub F E hs m) → F,
      ((∑ i, a i • b i : hermSub F E hs m) : Matrix (Fin m) (Fin m) E)
        = ∑ i, algebraMap F E (a i) • v i := by
    intro a
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Submodule.coe_smul, algebraMap_smul]
  have hherm : ∀ Y : hermSub F E hs m, (Y : Matrix (Fin m) (Fin m) E).conjTranspose = Y := fun Y => Y.2
  obtain ⟨u, hu⟩ := hδ
  have hli : LinearIndependent E v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    let H1 : hermSub F E hs m := ∑ i, β.repr (g i) 0 • b i
    let H2 : hermSub F E hs m := ∑ i, β.repr (g i) 1 • b i
    have e1 : (H1 : Matrix (Fin m) (Fin m) E) + ω • (H2 : Matrix (Fin m) (Fin m) E) = 0 := by
      rw [← hg, hcoe, hcoe, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      conv_rhs => rw [hj_decomp β ω h0 h1 (g i)]
      rw [add_smul, smul_smul, mul_comm ω]
    have e2 : (H1 : Matrix (Fin m) (Fin m) E) + star ω • (H2 : Matrix (Fin m) (Fin m) E) = 0 := by
      have := congrArg Matrix.conjTranspose e1
      rwa [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hherm, hherm,
        Matrix.conjTranspose_zero] at this
    have e3 : (u : E) • (H2 : Matrix (Fin m) (Fin m) E) = 0 := by
      rw [hu, sub_smul]
      have := congrArg₂ (· - ·) e1 e2
      simpa using this
    have e4 : (H2 : Matrix (Fin m) (Fin m) E) = 0 := by
      have := congrArg (fun X => ((u⁻¹ : Eˣ) : E) • X) e3
      simpa [smul_smul] using this
    have e5 : (H1 : Matrix (Fin m) (Fin m) E) = 0 := by
      rw [e4, smul_zero, add_zero] at e1; exact e1
    have hb := Fintype.linearIndependent_iff.1 b.linearIndependent
    have z1 := hb _ (Subtype.ext e5 : H1 = 0)
    have z2 := hb _ (Subtype.ext e4 : H2 = 0)
    intro i
    rw [hj_decomp β ω h0 h1 (g i), z1 i, z2 i]
    simp
  have hmem : ∀ Y : hermSub F E hs m,
      (Y : Matrix (Fin m) (Fin m) E) = ∑ i, algebraMap F E (b.repr Y i) • v i := by
    intro Y
    conv_lhs => rw [← b.sum_repr Y]
    exact hcoe _
  have hmem' : ∀ Y : hermSub F E hs m,
      (Y : Matrix (Fin m) (Fin m) E) ∈ Submodule.span E (Set.range v) := by
    intro Y
    rw [hmem Y]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hstu : star ((u⁻¹ : Eˣ) : E) = -((u⁻¹ : Eˣ) : E) := by
    have a1 : (u : E) * ((u⁻¹ : Eˣ) : E) = 1 := Units.mul_inv u
    have a2 : star (u : E) = -(u : E) := by rw [hu, star_sub, star_star]; ring
    have a3 : star (u : E) * star ((u⁻¹ : Eˣ) : E) = 1 := by rw [← star_mul', a1, star_one]
    rw [a2] at a3
    linear_combination (-((u⁻¹ : Eˣ) : E)) * a3 - (star ((u⁻¹ : Eˣ) : E)) * a1
  have hsp : ⊤ ≤ Submodule.span E (Set.range v) := by
    intro X _
    let X2 : Matrix (Fin m) (Fin m) E := ((u⁻¹ : Eˣ) : E) • (X - X.conjTranspose)
    have hX2 : X2.conjTranspose = X2 := by
      simp only [X2]
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
        hstu, neg_smul, ← smul_neg, neg_sub]
    have hX1 : (X - ω • X2).conjTranspose = X - ω • X2 := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hX2]
      have a1 : (u : E) • X2 = X - X.conjTranspose := by
        simp only [X2]; rw [smul_smul, Units.mul_inv, one_smul]
      rw [hu, sub_smul] at a1
      rw [sub_eq_sub_iff_add_eq_add]
      have := a1
      rw [sub_eq_sub_iff_add_eq_add] at this
      rw [add_comm, this, add_comm]
    have : X = (X - ω • X2) + ω • X2 := by abel
    rw [this]
    exact Submodule.add_mem _ (hmem' ⟨_, hX1⟩) (Submodule.smul_mem _ _ (hmem' ⟨_, hX2⟩))
  let bE := Module.Basis.mk hli hsp
  have hbE : ∀ i, bE i = v i := fun i => Module.Basis.mk_apply hli hsp i
  have hmat : LinearMap.toMatrix bE bE (rmulE m A ∘ₗ lmulE m A.conjTranspose)
      = (algebraMap F E).mapMatrix (LinearMap.toMatrix b b (congrHerm F E hs m A)) := by
    ext i j
    rw [LinearMap.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have e1 : (rmulE m A ∘ₗ lmulE m A.conjTranspose) (bE j)
        = ∑ i, algebraMap F E (b.repr (congrHerm F E hs m A (b j)) i) • bE i := by
      simp only [hbE]
      rw [← hmem]
      rfl
    rw [e1, Module.Basis.repr_sum_self]
  apply (algebraMap F E).injective
  rw [map_pow, hj_norm_star hs h2 hfix, ← det_congrE, ← LinearMap.det_toMatrix bE, hmat,
    ← RingHom.map_det, LinearMap.det_toMatrix]

end hermjacA2

/- English proof (translation)
Establish `hg' : W ≤ W.comap g` using `fun x hx => hW x hx`. Establish `hf' : W ≤ W.comap f` using `fun x hx => by`. Rewrite using `[Submodule.mem_comap, hfW x hx]`. Conclude with `hW x hx`. Rewrite using `[LinearMap.det_eq_det_mul_det W f hf', LinearMap.det_eq_det_mul_det W g hg']`.

Use `congr 2`. Conclude with `LinearMap.ext fun x => Subtype.ext (hfW x x.2)`. Apply `Submodule.linearMap_qext` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]`.

Conclude with `(Submodule.Quotient.eq W).2 (hfg x)`.
-/
lemma det_eq_of_agree {F V : Type} [Field F] [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) (f g : V →ₗ[F] V) (hW : ∀ x ∈ W, g x ∈ W) (hfW : ∀ x ∈ W, f x = g x)
    (hfg : ∀ x, f x - g x ∈ W) : LinearMap.det f = LinearMap.det g := by
  have hg' : W ≤ W.comap g := fun x hx => hW x hx
  have hf' : W ≤ W.comap f := fun x hx => by
    rw [Submodule.mem_comap, hfW x hx]; exact hW x hx
  rw [LinearMap.det_eq_det_mul_det W f hf', LinearMap.det_eq_det_mul_det W g hg']
  congr 2
  · exact LinearMap.ext fun x => Subtype.ext (hfW x x.2)
  · apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    exact (Submodule.Quotient.eq W).2 (hfg x)

section hermjacB
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]

omit [StarRing E] in

noncomputable def dualNumberReal (β : Module.Basis (Fin 2) F E) (ε : E) (h0 : β 0 = 1) (h1 : β 1 = ε) (hε : ε * ε = 0) :
    E →+* F where
  toFun e := β.repr e 0
  map_one' := by
    have := (hj_repr β ε h0 h1 1 0).1
    simpa using this
  map_mul' x y := by
    have e1 : x * y = algebraMap F E (β.repr x 0 * β.repr y 0)
        + algebraMap F E (β.repr x 0 * β.repr y 1 + β.repr x 1 * β.repr y 0) * ε := by
      conv_lhs => rw [hj_decomp β ε h0 h1 x, hj_decomp β ε h0 h1 y]
      simp only [map_mul, map_add]
      linear_combination (algebraMap F E (β.repr x 1) * algebraMap F E (β.repr y 1)) * hε
    conv_lhs => rw [e1]
    exact (hj_repr β ε h0 h1 _ _).1
  map_zero' := by simp
  map_add' x y := by simp

/- English proof (translation)
Establish `: Module.Finite F E` using `Module.Finite.of_basis β`. Set `π0` to `dualNumberReal β ε h0 h1 hε`. Establish `hπ0 : ∀ e, π0 e = β.repr e 0` using `fun e => rfl`. Establish `hrep0 : ∀ a b : F, π0 (algebraMap F E a + algebraMap F E b * ε) = a` using `fun a b => (hj_repr β ε h0 h1 a b).1`. Establish `hrep1 : ∀ a b : F, β.repr (algebraMap F E a + algebraMap F E b * ε) 1 = b` using `fun a b => (hj_repr β ε h0 h1 a b).2`.

Establish `hdec : ∀ e, e = algebraMap F E (π0 e) + algebraMap F E (β.repr e 1) * ε` using `hj_decomp β ε h0 h1`. Establish `hst : ∀ e, star e = algebraMap F E (π0 e) + algebraMap F E (-(β.repr e 1)) * ε`. Introduce `e`. Use `conv_lhs => rw [hdec e]`. Rewrite using `[star_add, star_mul', hs, hs, hstar, map_neg]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hπ0st : ∀ e, π0 (star e) = π0 e` using `fun e => by rw [hst e, hrep0]`. Establish `hπ1st : ∀ e, β.repr (star e) 1 = -(β.repr e 1)` using `fun e => by rw [hst e, hrep1]`. Establish `hεe : ∀ e, ε * e = ε * algebraMap F E (π0 e)`. Introduce `e`.

Use `conv_lhs => rw [hdec e]`. Take the linear combination `(algebraMap F E (β.repr e 1)) * hε`. Set `A0 : Matrix (Fin m) (Fin m) F` to `π0.mapMatrix A`. Set `Φ0 : Matrix (Fin m) (Fin m) F →ₗ[F] Matrix (Fin m) (Fin m) E` to `{ toFun := fun Y => Matrix.of fun i j => algebraMap F E (Y i j + Y j i) + algebraMap F E (Y i j - Y j i) * ε map_add' := fun Y Z => by`. Use extensionality with `i j`.

Simplify using `only [Matrix.of_apply, Matrix.add_apply, map_add, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := fun c Y => by`. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, map_add, map_sub, map_mul, Algebra.smul_def]`.

Use `ring }`. Establish `hΦ0 : ∀ Y i j, Φ0 Y i j = algebraMap F E (Y i j + Y j i) + algebraMap F E (Y i j - Y j i) * ε` using `fun Y i j => rfl`. Establish `hΦH : ∀ Y, Φ0 Y ∈ hermSub F E hs m`. Introduce `Y`. Express the relevant statement in the definitionally equal form `(Φ0 Y).conjTranspose = Φ0 Y`.

Use extensionality with `i j`. Rewrite using `[Matrix.conjTranspose_apply, hΦ0, hΦ0, star_add, star_mul', hs, hs, hstar]`. Simplify using `only [map_add, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Set `Φl : Matrix (Fin m) (Fin m) F →ₗ[F] hermSub F E hs m` to `LinearMap.codRestrict _ Φ0 hΦH`.

Establish `hinj : Function.Injective Φl`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `Y hY`. Establish `hY0 : Φ0 Y = 0` using `congrArg Subtype.val hY`. Use extensionality with `i j`.

Establish `e` using `congrFun (congrFun hY0 i) j`. Rewrite `e` using `[hΦ0]`. Establish `e0` using `hrep0 (Y i j + Y j i) (Y i j - Y j i)`. Establish `e1` using `hrep1 (Y i j + Y j i) (Y i j - Y j i)`. Rewrite `e0`, `e1` using `[e]`.

Simplify using `only [Matrix.zero_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply] at e0 e1`. Establish `: (2 : F) * Y i j = 0` using `by linear_combination -e0 - e1`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `absurd h htwo`. Simplify using `using h`.

Establish `hsurj : Function.Surjective Φl`. Introduce `X`. Establish `hX : ∀ i j, (X : Matrix (Fin m) (Fin m) E) j i = star ((X : Matrix (Fin m) (Fin m) E) i j)`. Introduce `i j`. Use `congrFun (congrFun X.2 j) i` as an intermediate fact.

Rewrite `this` using `[Matrix.conjTranspose_apply]`. Conclude with `this.symm`. Use `⟨Matrix.of fun i j => (π0 ((X : Matrix (Fin m) (Fin m) E) i j) + β.repr ((X : Matrix (Fin m) (Fin m) E) i j) 1) / 2, Subtype.ext ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `Φ0 _ i j = _`.

Rewrite using `[hΦ0]`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[hX i j, hπ0st, hπ1st]`. Use `conv_rhs => rw [hdec ((X : Matrix (Fin m) (Fin m) E) i j)]`. Establish `ea : ∀ a b : F, (a + b) / 2 + (a + -b) / 2 = a` using `fun a b => by field_simp; ring`.

Establish `eb : ∀ a b : F, (a + b) / 2 - (a + -b) / 2 = b` using `fun a b => by field_simp; ring`. Rewrite using `[ea, eb]`. Set `Φ : Matrix (Fin m) (Fin m) F ≃ₗ[F] hermSub F E hs m` to `LinearEquiv.ofBijective Φl ⟨hinj, hsurj⟩`. Establish `hΦ : ∀ Y, ((Φ Y : hermSub F E hs m) : Matrix (Fin m) (Fin m) E) = Φ0 Y` using `fun Y => rfl`. Establish `hP0Φ : ∀ Y, π0.mapMatrix (Φ0 Y) = Y + Y.transpose`.

Introduce `Y`. Use extensionality with `i j`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, hΦ0, hrep0]`. Both sides reduce to the same expression. Establish `hP0H : π0.mapMatrix A.conjTranspose = A0.transpose`.

Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, A0, hπ0st]`. Set `c0 : Matrix (Fin m) (Fin m) F →ₗ[F] Matrix (Fin m) (Fin m) F` to `rmulE m A0 ∘ₗ lmulE m A0.transpose`. Establish `hc0 : ∀ Y, c0 Y = A0.transpose * Y * A0` using `fun Y => rfl`. Establish `hc0T : ∀ Y, c0 Y + (c0 Y).transpose = A0.transpose * (Y + Y.transpose) * A0`.

Introduce `Y`. Rewrite using `[hc0, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc A0.transpose Y.transpose]`. Set `f' : Matrix (Fin m) (Fin m) F →ₗ[F] Matrix (Fin m) (Fin m) F` to `(Φ.symm : _ →ₗ[F] _) ∘ₗ congrHerm F E hs m A ∘ₗ (Φ.symm.symm : _ →ₗ[F] _)`. Establish `hf' : ∀ Y, Φ0 (f' Y) = A.conjTranspose * Φ0 Y * A`. Introduce `Y`.

Rewrite using `[← hΦ]`. Express the relevant statement in the definitionally equal form `((Φ (Φ.symm (congrHerm F E hs m A (Φ Y))) : hermSub F E hs m) : Matrix (Fin m) (Fin m) E) = _`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression. Establish `hdet1 : LinearMap.det f' = LinearMap.det (congrHerm F E hs m A)` using `LinearMap.det_conj _ _`.

Set `W : Submodule F (Matrix (Fin m) (Fin m) F)` to `{ carrier := {Y | Y + Y.transpose = 0} add_mem' := fun {a b} ha hb => by`. Express the relevant statement in the definitionally equal form `a + b + (a + b).transpose = 0`. Establish `ha' : a + a.transpose = 0` using `ha`. Establish `hb' : b + b.transpose = 0` using `hb`. Rewrite using `[Matrix.transpose_add, add_add_add_comm, ha', hb', add_zero]`.

Use the proof step `zero_mem' := by`. Express the relevant statement in the definitionally equal form `(0 : Matrix (Fin m) (Fin m) F) + (0 : Matrix (Fin m) (Fin m) F).transpose = 0`. Simplify using the standard rewrite rules. Use the proof step `smul_mem' := fun c a ha => by`. Express the relevant statement in the definitionally equal form `c • a + (c • a).transpose = 0`.

Establish `ha' : a + a.transpose = 0` using `ha`. Rewrite using `[Matrix.transpose_smul, ← smul_add, ha', smul_zero] }`. Establish `hdet2 : LinearMap.det f' = LinearMap.det c0`. Apply `det_eq_of_agree W f' c0` to reduce the goal to its premises. Introduce `Y hY`.

Express the relevant statement in the definitionally equal form `c0 Y + (c0 Y).transpose = 0`. Establish `hY' : Y + Y.transpose = 0` using `hY`. Rewrite using `[hc0T, hY', Matrix.mul_zero, Matrix.zero_mul]`. Introduce `Y hY`. Establish `hY' : Y + Y.transpose = 0` using `hY`.

Establish `hinj0 : Function.Injective Φ0` using `fun a b hab => hinj (Subtype.ext hab)`. Apply `hinj0` to reduce the goal to its premises. Rewrite using `[hf']`. Establish `eform : ∀ Z : Matrix (Fin m) (Fin m) F, Z + Z.transpose = 0 → Φ0 Z = ε • (algebraMap F E).mapMatrix (Z - Z.transpose)`. Introduce `Z hZ`.

Use extensionality with `i j`. Establish `hz : Z i j + Z j i = 0` using `congrFun (congrFun hZ i) j`. Rewrite using `[hΦ0, hz, map_zero, zero_add, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression. Establish `hεX : ∀ X : Matrix (Fin m) (Fin m) E, ε • X = ε • (algebraMap F E).mapMatrix (π0.mapMatrix X)`.

Introduce `X`. Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]`. Conclude with `hεe _`. Establish `hc0W : c0 Y + (c0 Y).transpose = 0`.

Rewrite using `[hc0T, hY', Matrix.mul_zero, Matrix.zero_mul]`. Rewrite using `[eform Y hY', eform (c0 Y) hc0W, Matrix.mul_smul, Matrix.smul_mul, hεX]`. Use `congr 2`. Rewrite using `[map_mul, map_mul, hP0H]`. Establish `e3 : π0.mapMatrix ((algebraMap F E).mapMatrix (Y - Y.transpose)) = Y - Y.transpose`.

Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply]`. Use `hrep0 ((Y - Y.transpose) i j) 0` as an intermediate fact. Simplify using `using this`. Rewrite using `[e3, hc0, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc A0.transpose Y.transpose]`.

Introduce `Y`. Express the relevant statement in the definitionally equal form `(f' Y - c0 Y) + (f' Y - c0 Y).transpose = 0`. Establish `e1 : f' Y + (f' Y).transpose = A0.transpose * (Y + Y.transpose) * A0`. Rewrite using `[← hP0Φ, hf', map_mul, map_mul, hP0H, hP0Φ]`. Rewrite using `[Matrix.transpose_sub, sub_add_sub_comm, e1, hc0T, sub_self]`.

Establish `hdet3 : LinearMap.det c0 = (A0.det ^ 2) ^ m`. Rewrite using `[LinearMap.det_comp, det_rmulE, det_lmulE, Matrix.det_transpose, ← mul_pow, sq]`. Establish `hnorm : Algebra.norm F A.det = A0.det ^ 2`. Establish `e1 : A0.det = π0 A.det` using `(RingHom.map_det π0 A).symm`. Rewrite using `[hdec A.det, hj_norm β ε h0 h1 0 0 (by rw [hε]; simp), ← e1]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hdet1, hdet2, hdet3, hnorm]`.
-/
lemma hj_caseB (hs : ∀ c : F, star (algebraMap F E c) = algebraMap F E c)
    (ε : E) (β : Module.Basis (Fin 2) F E) (h0 : β 0 = 1) (h1 : β 1 = ε)
    (hε : ε * ε = 0) (hstar : star ε = -ε) (htwo : (2 : F) ≠ 0) (m : ℕ)
    (A : Matrix (Fin m) (Fin m) E) :
    LinearMap.det (congrHerm F E hs m A) = Algebra.norm F A.det ^ m := by
  classical
  have : Module.Finite F E := Module.Finite.of_basis β
  let π0 := dualNumberReal β ε h0 h1 hε
  have hπ0 : ∀ e, π0 e = β.repr e 0 := fun e => rfl
  have hrep0 : ∀ a b : F, π0 (algebraMap F E a + algebraMap F E b * ε) = a := fun a b =>
    (hj_repr β ε h0 h1 a b).1
  have hrep1 : ∀ a b : F, β.repr (algebraMap F E a + algebraMap F E b * ε) 1 = b := fun a b =>
    (hj_repr β ε h0 h1 a b).2
  have hdec : ∀ e, e = algebraMap F E (π0 e) + algebraMap F E (β.repr e 1) * ε :=
    hj_decomp β ε h0 h1
  have hst : ∀ e, star e = algebraMap F E (π0 e) + algebraMap F E (-(β.repr e 1)) * ε := by
    intro e
    conv_lhs => rw [hdec e]
    rw [star_add, star_mul', hs, hs, hstar, map_neg]; ring
  have hπ0st : ∀ e, π0 (star e) = π0 e := fun e => by rw [hst e, hrep0]
  have hπ1st : ∀ e, β.repr (star e) 1 = -(β.repr e 1) := fun e => by rw [hst e, hrep1]
  have hεe : ∀ e, ε * e = ε * algebraMap F E (π0 e) := by
    intro e
    conv_lhs => rw [hdec e]
    linear_combination (algebraMap F E (β.repr e 1)) * hε
  let A0 : Matrix (Fin m) (Fin m) F := π0.mapMatrix A

  let Φ0 : Matrix (Fin m) (Fin m) F →ₗ[F] Matrix (Fin m) (Fin m) E :=
    { toFun := fun Y => Matrix.of fun i j =>
        algebraMap F E (Y i j + Y j i) + algebraMap F E (Y i j - Y j i) * ε
      map_add' := fun Y Z => by
        ext i j
        simp only [Matrix.of_apply, Matrix.add_apply, map_add, map_sub]; ring
      map_smul' := fun c Y => by
        ext i j
        simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, map_add,
          map_sub, map_mul, Algebra.smul_def]
        ring }
  have hΦ0 : ∀ Y i j, Φ0 Y i j
      = algebraMap F E (Y i j + Y j i) + algebraMap F E (Y i j - Y j i) * ε := fun Y i j => rfl
  have hΦH : ∀ Y, Φ0 Y ∈ hermSub F E hs m := by
    intro Y
    change (Φ0 Y).conjTranspose = Φ0 Y
    ext i j
    rw [Matrix.conjTranspose_apply, hΦ0, hΦ0, star_add, star_mul', hs, hs, hstar]
    simp only [map_add, map_sub]; ring
  let Φl : Matrix (Fin m) (Fin m) F →ₗ[F] hermSub F E hs m := LinearMap.codRestrict _ Φ0 hΦH
  have hinj : Function.Injective Φl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Y hY
    have hY0 : Φ0 Y = 0 := congrArg Subtype.val hY
    ext i j
    have e := congrFun (congrFun hY0 i) j
    rw [hΦ0] at e
    have e0 := hrep0 (Y i j + Y j i) (Y i j - Y j i)
    have e1 := hrep1 (Y i j + Y j i) (Y i j - Y j i)
    rw [e] at e0 e1
    simp only [Matrix.zero_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply] at e0 e1
    have : (2 : F) * Y i j = 0 := by linear_combination -e0 - e1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h htwo
    · simpa using h
  have hsurj : Function.Surjective Φl := by
    intro X
    have hX : ∀ i j, (X : Matrix (Fin m) (Fin m) E) j i = star ((X : Matrix (Fin m) (Fin m) E) i j) := by
      intro i j
      have := congrFun (congrFun X.2 j) i
      rw [Matrix.conjTranspose_apply] at this
      exact this.symm
    refine ⟨Matrix.of fun i j => (π0 ((X : Matrix (Fin m) (Fin m) E) i j)
      + β.repr ((X : Matrix (Fin m) (Fin m) E) i j) 1) / 2, Subtype.ext ?_⟩
    ext i j
    change Φ0 _ i j = _
    rw [hΦ0]
    simp only [Matrix.of_apply]
    rw [hX i j, hπ0st, hπ1st]
    conv_rhs => rw [hdec ((X : Matrix (Fin m) (Fin m) E) i j)]
    have ea : ∀ a b : F, (a + b) / 2 + (a + -b) / 2 = a := fun a b => by field_simp; ring
    have eb : ∀ a b : F, (a + b) / 2 - (a + -b) / 2 = b := fun a b => by field_simp; ring
    rw [ea, eb]
  let Φ : Matrix (Fin m) (Fin m) F ≃ₗ[F] hermSub F E hs m := LinearEquiv.ofBijective Φl ⟨hinj, hsurj⟩
  have hΦ : ∀ Y, ((Φ Y : hermSub F E hs m) : Matrix (Fin m) (Fin m) E) = Φ0 Y := fun Y => rfl
  have hP0Φ : ∀ Y, π0.mapMatrix (Φ0 Y) = Y + Y.transpose := by
    intro Y
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hΦ0, hrep0]
    rfl
  have hP0H : π0.mapMatrix A.conjTranspose = A0.transpose := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.conjTranspose_apply,
      Matrix.transpose_apply, A0, hπ0st]
  let c0 : Matrix (Fin m) (Fin m) F →ₗ[F] Matrix (Fin m) (Fin m) F :=
    rmulE m A0 ∘ₗ lmulE m A0.transpose
  have hc0 : ∀ Y, c0 Y = A0.transpose * Y * A0 := fun Y => rfl
  have hc0T : ∀ Y, c0 Y + (c0 Y).transpose = A0.transpose * (Y + Y.transpose) * A0 := by
    intro Y
    rw [hc0, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc A0.transpose Y.transpose]
  let f' : Matrix (Fin m) (Fin m) F →ₗ[F] Matrix (Fin m) (Fin m) F :=
    (Φ.symm : _ →ₗ[F] _) ∘ₗ congrHerm F E hs m A ∘ₗ (Φ.symm.symm : _ →ₗ[F] _)
  have hf' : ∀ Y, Φ0 (f' Y) = A.conjTranspose * Φ0 Y * A := by
    intro Y
    rw [← hΦ]
    change ((Φ (Φ.symm (congrHerm F E hs m A (Φ Y))) : hermSub F E hs m) : Matrix (Fin m) (Fin m) E) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hdet1 : LinearMap.det f' = LinearMap.det (congrHerm F E hs m A) := LinearMap.det_conj _ _
  let W : Submodule F (Matrix (Fin m) (Fin m) F) :=
    { carrier := {Y | Y + Y.transpose = 0}
      add_mem' := fun {a b} ha hb => by
        change a + b + (a + b).transpose = 0
        have ha' : a + a.transpose = 0 := ha
        have hb' : b + b.transpose = 0 := hb
        rw [Matrix.transpose_add, add_add_add_comm, ha', hb', add_zero]
      zero_mem' := by
        change (0 : Matrix (Fin m) (Fin m) F) + (0 : Matrix (Fin m) (Fin m) F).transpose = 0
        simp
      smul_mem' := fun c a ha => by
        change c • a + (c • a).transpose = 0
        have ha' : a + a.transpose = 0 := ha
        rw [Matrix.transpose_smul, ← smul_add, ha', smul_zero] }
  have hdet2 : LinearMap.det f' = LinearMap.det c0 := by
    apply det_eq_of_agree W f' c0
    · intro Y hY
      change c0 Y + (c0 Y).transpose = 0
      have hY' : Y + Y.transpose = 0 := hY
      rw [hc0T, hY', Matrix.mul_zero, Matrix.zero_mul]
    · intro Y hY
      have hY' : Y + Y.transpose = 0 := hY
      have hinj0 : Function.Injective Φ0 := fun a b hab => hinj (Subtype.ext hab)
      apply hinj0
      rw [hf']
      have eform : ∀ Z : Matrix (Fin m) (Fin m) F, Z + Z.transpose = 0 →
          Φ0 Z = ε • (algebraMap F E).mapMatrix (Z - Z.transpose) := by
        intro Z hZ
        ext i j
        have hz : Z i j + Z j i = 0 := congrFun (congrFun hZ i) j
        rw [hΦ0, hz, map_zero, zero_add, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
          smul_eq_mul, mul_comm]
        rfl
      have hεX : ∀ X : Matrix (Fin m) (Fin m) E,
          ε • X = ε • (algebraMap F E).mapMatrix (π0.mapMatrix X) := by
        intro X
        ext i j
        simp only [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
        exact hεe _
      have hc0W : c0 Y + (c0 Y).transpose = 0 := by
        rw [hc0T, hY', Matrix.mul_zero, Matrix.zero_mul]
      rw [eform Y hY', eform (c0 Y) hc0W, Matrix.mul_smul, Matrix.smul_mul, hεX]
      congr 2
      rw [map_mul, map_mul, hP0H]
      have e3 : π0.mapMatrix ((algebraMap F E).mapMatrix (Y - Y.transpose)) = Y - Y.transpose := by
        ext i j
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
        have := hrep0 ((Y - Y.transpose) i j) 0
        simpa using this
      rw [e3, hc0, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc A0.transpose Y.transpose]
    · intro Y
      change (f' Y - c0 Y) + (f' Y - c0 Y).transpose = 0
      have e1 : f' Y + (f' Y).transpose = A0.transpose * (Y + Y.transpose) * A0 := by
        rw [← hP0Φ, hf', map_mul, map_mul, hP0H, hP0Φ]
      rw [Matrix.transpose_sub, sub_add_sub_comm, e1, hc0T, sub_self]
  have hdet3 : LinearMap.det c0 = (A0.det ^ 2) ^ m := by
    rw [LinearMap.det_comp, det_rmulE, det_lmulE, Matrix.det_transpose, ← mul_pow, sq]
  have hnorm : Algebra.norm F A.det = A0.det ^ 2 := by
    have e1 : A0.det = π0 A.det := (RingHom.map_det π0 A).symm
    rw [hdec A.det, hj_norm β ε h0 h1 0 0 (by rw [hε]; simp), ← e1]
    ring
  rw [← hdet1, hdet2, hdet3, hnorm]

end hermjacB

/- English proof (translation)
Introduce `F E _ _ _ _ hs h2 hfix m A`. Establish `: Nontrivial E` using `Module.nontrivial_of_finrank_pos (R := F) (by rw [h2]; norm_num)`. Take `⟨ω, hω⟩` from `hj_exists_omega (F := F) (E := E) h2`. Take `⟨β, h0, h1⟩` from `hj_basis h2 ω hω`. Establish `hstδ : star (ω - star ω) = -(ω - star ω)` using `by rw [star_sub, star_star]; ring`.

Take `⟨e2, he2⟩` from `hfix ((ω - star ω) * (ω - star ω)) (by rw [star_mul', hstδ]; ring)`. Distinguish the cases in `hz : e2 = 0`. Establish `hε : (ω - star ω) * (ω - star ω) = 0` using `by rw [← he2, hz, map_zero]`. Establish `hne : ω - star ω ≠ 0`. Introduce `h`.

Take `⟨c, hc⟩` from `hfix ω (sub_eq_zero.1 h).symm`. Conclude with `hω c hc`. Take `⟨t, ht⟩` from `hfix (ω + star ω) (by rw [star_add, star_star, add_comm])`. Establish `htwo : (2 : F) ≠ 0`. Introduce `h2F`.

Establish `h2E : (2 : E) = 0`. Use `congrArg (algebraMap F E) h2F` as an intermediate fact. Rewrite `this` using `[map_ofNat, map_zero]`. Conclude with `this`. Establish `e1 : ω - star ω = algebraMap F E t`.

Rewrite using `[ht]`. Take the linear combination `(-(star ω)) * h2E`. Rewrite `hε` using `[e1, ← map_mul]`. Establish `: t * t = 0` using `(map_eq_zero_iff _ (algebraMap F E).injective).1 hε`. Establish `ht0 : t = 0` using `mul_self_eq_zero.1 this`.

Rewrite `e1` using `[ht0, map_zero]`. Conclude with `hne e1`. Establish `hεF : ∀ c : F, algebraMap F E c ≠ ω - star ω`. Introduce `c hc`. Establish `e1 : star (ω - star ω) = ω - star ω` using `by rw [← hc, hs]`.

Rewrite `e1` using `[hstδ]`. Establish `e3 : algebraMap F E 2 * (ω - star ω) = 0`. Rewrite using `[map_ofNat]`. Take the linear combination `-e1`. Establish `e4 : algebraMap F E 2⁻¹ * algebraMap F E 2 = 1`.

Rewrite using `[← map_mul, inv_mul_cancel₀ htwo, map_one]`. Apply `hne` to reduce the goal to its premises. Take the linear combination `(algebraMap F E 2⁻¹) * e3 - (ω - star ω) * e4`. Take `⟨β', h0', h1'⟩` from `hj_basis h2 (ω - star ω) hεF`. Conclude with `hj_caseB hs (ω - star ω) β' h0' h1' hε hstδ htwo m A`.

Establish `hδ : IsUnit (ω - star ω)`. Use `IsUnit.of_mul_eq_one ((ω - star ω) * algebraMap F E e2⁻¹) ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← he2, ← map_mul, mul_inv_cancel₀ hz, map_one]`. Conclude with `hj_caseA hs h2 hfix ω β h0 h1 hδ m A`.
-/
theorem hermitian_jacobian : HermJac := by
  intro F E _ _ _ _ hs h2 hfix m A
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [h2]; norm_num)
  obtain ⟨ω, hω⟩ := hj_exists_omega (F := F) (E := E) h2
  obtain ⟨β, h0, h1⟩ := hj_basis h2 ω hω
  have hstδ : star (ω - star ω) = -(ω - star ω) := by rw [star_sub, star_star]; ring
  obtain ⟨e2, he2⟩ := hfix ((ω - star ω) * (ω - star ω)) (by rw [star_mul', hstδ]; ring)
  by_cases hz : e2 = 0
  ·
    have hε : (ω - star ω) * (ω - star ω) = 0 := by rw [← he2, hz, map_zero]
    have hne : ω - star ω ≠ 0 := by
      intro h
      obtain ⟨c, hc⟩ := hfix ω (sub_eq_zero.1 h).symm
      exact hω c hc
    obtain ⟨t, ht⟩ := hfix (ω + star ω) (by rw [star_add, star_star, add_comm])
    have htwo : (2 : F) ≠ 0 := by
      intro h2F
      have h2E : (2 : E) = 0 := by
        have := congrArg (algebraMap F E) h2F
        rw [map_ofNat, map_zero] at this
        exact this
      have e1 : ω - star ω = algebraMap F E t := by
        rw [ht]; linear_combination (-(star ω)) * h2E
      rw [e1, ← map_mul] at hε
      have : t * t = 0 := (map_eq_zero_iff _ (algebraMap F E).injective).1 hε
      have ht0 : t = 0 := mul_self_eq_zero.1 this
      rw [ht0, map_zero] at e1
      exact hne e1
    have hεF : ∀ c : F, algebraMap F E c ≠ ω - star ω := by
      intro c hc
      have e1 : star (ω - star ω) = ω - star ω := by rw [← hc, hs]
      rw [hstδ] at e1
      have e3 : algebraMap F E 2 * (ω - star ω) = 0 := by
        rw [map_ofNat]; linear_combination -e1
      have e4 : algebraMap F E 2⁻¹ * algebraMap F E 2 = 1 := by
        rw [← map_mul, inv_mul_cancel₀ htwo, map_one]
      apply hne
      linear_combination (algebraMap F E 2⁻¹) * e3 - (ω - star ω) * e4
    obtain ⟨β', h0', h1'⟩ := hj_basis h2 (ω - star ω) hεF
    exact hj_caseB hs (ω - star ω) β' h0' h1' hε hstδ htwo m A
  · have hδ : IsUnit (ω - star ω) := by
      refine IsUnit.of_mul_eq_one ((ω - star ω) * algebraMap F E e2⁻¹) ?_
      rw [← mul_assoc, ← he2, ← map_mul, mul_inv_cancel₀ hz, map_one]
    exact hj_caseA hs h2 hfix ω β h0 h1 hδ m A

end Formalism.HermitianLatticeCounting.P.S4aux

namespace Formalism.HermitianLatticeCounting.P

/- English proof (translation)
The claim follows from `S4aux.projection_weight_formula`.
-/
theorem projection_weight_formula : Formalism.HermitianLatticeCounting.S4.ProjW := S4aux.projection_weight_formula
/- English proof (translation)
The claim follows from `S4aux.pair_second_constant`.
-/
theorem pair_second_constant : Formalism.HermitianLatticeCounting.S4.PairingOrthogonalComplement := S4aux.pair_second_constant
/- English proof (translation)
The claim follows from `S4aux.leakage_algebraic_identity`.
-/
theorem leakage_algebraic_identity : Formalism.HermitianLatticeCounting.S4.LeakAlg := S4aux.leakage_algebraic_identity
/- English proof (translation)
The claim follows from `S4aux.move_second_coordinate`.
-/
theorem move_second_coordinate : Formalism.HermitianLatticeCounting.S4.MoveY := S4aux.move_second_coordinate
/- English proof (translation)
The claim follows from `S4aux.move_preserves_weight`.
-/
theorem move_preserves_weight : Formalism.HermitianLatticeCounting.S4.MoveWeight := S4aux.move_preserves_weight
/- English proof (translation)
The claim follows from `S4aux.move_congruence`.
-/
theorem move_congruence : Formalism.HermitianLatticeCounting.S4.MoveCong := S4aux.move_congruence
/- English proof (translation)
The claim follows from `S4aux.move_involutive`.
-/
theorem move_involutive : Formalism.HermitianLatticeCounting.S4.MoveInvol := S4aux.move_involutive
/- English proof (translation)
The claim follows from `S4aux.move_perpendicular`.
-/
theorem move_perpendicular : Formalism.HermitianLatticeCounting.S4.MovePerp := S4aux.move_perpendicular
/- English proof (translation)
The claim follows from `S4aux.type_class_count`.
-/
theorem type_class_count : Formalism.HermitianLatticeCounting.S4.TypeBeClass := S4aux.type_class_count
/- English proof (translation)
The claim follows from `S4aux.kernel_average`.
-/
theorem kernel_average : Formalism.HermitianLatticeCounting.S4.KernelAvg := S4aux.kernel_average
/- English proof (translation)
The claim follows from `S4aux.leakage_back_map`.
-/
theorem leakage_back_map : Formalism.HermitianLatticeCounting.S4.LeakBack := S4aux.leakage_back_map
/- English proof (translation)
The claim follows from `S4aux.primitive_cancellation`.
-/
theorem primitive_cancellation : Formalism.HermitianLatticeCounting.S4.PrimCancel := S4aux.primitive_cancellation
/- English proof (translation)
The claim follows from `S4aux.maximal_sum_bound`.
-/
theorem maximal_sum_bound : Formalism.HermitianLatticeCounting.S4.MaxSum := S4aux.maximal_sum_bound
/- English proof (translation)
The claim follows from `S4aux.superdiagonal_addition_invariance`.
-/
theorem superdiagonal_addition_invariance : Formalism.HermitianLatticeCounting.S4.SuperDiagAdd := S4aux.superdiagonal_addition_invariance
/- English proof (translation)
The claim follows from `S4aux.involution_well_defined`.
-/
theorem involution_well_defined : Formalism.HermitianLatticeCounting.S4.TauWell := S4aux.involution_well_defined
/- English proof (translation)
The claim follows from `S4aux.orbit_count_formula`.
-/
theorem orbit_count_formula : Formalism.HermitianLatticeCounting.S4.OmCount := S4aux.orbit_count_formula
/- English proof (translation)
The claim follows from `S4aux.gauss_summand_formula`.
-/
theorem gauss_summand_formula : Formalism.HermitianLatticeCounting.S4.GaussSummand := S4aux.gauss_summand_formula
/- English proof (translation)
The claim follows from `S4aux.homomorphism_count`.
-/
theorem hom_count_symmetric_group : Formalism.HermitianLatticeCounting.S4.HomCount := S4aux.homomorphism_count
/- English proof (translation)
The claim follows from `S4aux.overlattice_count_formula`.
-/
theorem overlattice_count_formula : Formalism.HermitianLatticeCounting.S4.OverlatticeCount := S4aux.overlattice_count_formula
/- English proof (translation)
The claim follows from `S4aux.weighted_cauchy_schwarz`.
-/
theorem weighted_cauchy_schwarz : Formalism.HermitianLatticeCounting.S4.WeightedCS := S4aux.weighted_cauchy_schwarz
/- English proof (translation)
The claim follows from `S4aux.type_cauchy_schwarz`.
-/
theorem type_cauchy_schwarz : Formalism.HermitianLatticeCounting.S4.TypeCS := S4aux.type_cauchy_schwarz
/- English proof (translation)
The claim follows from `S4aux.kernel_average_sum`.
-/
theorem kernel_average_sum : Formalism.HermitianLatticeCounting.S4.KernelAvgSum := S4aux.kernel_average_sum
/- English proof (translation)
The claim follows from `S4aux.hermitian_count_assembly`.
-/
theorem hermitian_count_assembly : Formalism.HermitianLatticeCounting.S4.AssemblyNG := S4aux.hermitian_count_assembly
/- English proof (translation)
The claim follows from `S4aux.fourth_reduction_identity`.
-/
theorem fourth_reduction_identity : Formalism.HermitianLatticeCounting.S4.Step4 := S4aux.fourth_reduction_identity
/- English proof (translation)
The claim follows from `S4aux.gauss_sum_share`.
-/
theorem gauss_sum_share : Formalism.HermitianLatticeCounting.S4.GaussShare := S4aux.gauss_sum_share
/- English proof (translation)
The claim follows from `S4aux.leakage_share_bound_alt`.
-/
theorem leakage_share_bound_alt : Formalism.HermitianLatticeCounting.S4.LeakShare := S4aux.leakage_share_bound_alt
/- English proof (translation)
The claim follows from `S4aux.span_character_ring`.
-/
theorem span_character_ring : Formalism.HermitianLatticeCounting.S4.SpanCharRing := S4aux.span_character_ring
/- English proof (translation)
The claim follows from `S4aux.determinant_annihilates`.
-/
theorem determinant_annihilates : Formalism.HermitianLatticeCounting.S4.DetKills := S4aux.determinant_annihilates
/- English proof (translation)
The claim follows from `S4aux.unimodular_split`.
-/
theorem unimodular_split : Formalism.HermitianLatticeCounting.S4.UnimodSplit := S4aux.unimodular_split
/- English proof (translation)
The claim follows from `S4aux.local_density_product`.
-/
theorem local_density_product : Formalism.HermitianLatticeCounting.S4.ValuationProductBound := S4aux.local_density_product
/- English proof (translation)
The claim follows from `S4aux.isotropic_complement`.
-/
theorem isotropic_complement : Formalism.HermitianLatticeCounting.S4.IsoComplement := S4aux.isotropic_complement
/- English proof (translation)
The claim follows from `S4aux.tuple_jacobian_alt`.
-/
theorem tuple_jacobian_alt : Formalism.HermitianLatticeCounting.S4.TupleJac := S4aux.tuple_jacobian_alt
/- English proof (translation)
The claim follows from `S4aux.class_number_squares`.
-/
theorem class_number_squares : Formalism.HermitianLatticeCounting.S4.ClassSquares := S4aux.class_number_squares
/- English proof (translation)
The claim follows from `S4aux.hermitian_gauss_sum_ring`.
-/
theorem hermitian_gauss_sum_ring : Formalism.HermitianLatticeCounting.S4.HermGaussRing := S4aux.hermitian_gauss_sum_ring
/- English proof (translation)
The claim follows from `S4aux.proper_index_formula`.
-/
theorem proper_index_formula : Formalism.HermitianLatticeCounting.S4.ProperIndex := S4aux.proper_index_formula
/- English proof (translation)
The claim follows from `S4aux.divisor_count_bound`.
-/
theorem divisor_count_bound : Formalism.HermitianLatticeCounting.S4.DivisorCount := S4aux.divisor_count_bound
/- English proof (translation)
The claim follows from `S4aux.unfolding_symmetric`.
-/
theorem unfolding_symmetric : Formalism.HermitianLatticeCounting.S4.UnfoldSym := S4aux.unfolding_symmetric
/- English proof (translation)
The claim follows from `S4aux.dual_capacity_formula`.
-/
theorem dual_capacity_formula : Formalism.HermitianLatticeCounting.S4.DualCap := S4aux.dual_capacity_formula
/- English proof (translation)
The claim follows from `S4aux.same_trace_count`.
-/
theorem same_trace_count : Formalism.HermitianLatticeCounting.S4.SameTrace := S4aux.same_trace_count
/- English proof (translation)
The claim follows from `S4aux.hermitian_count_equality`.
-/
theorem hermitian_count_equality : Formalism.HermitianLatticeCounting.S4.EqualityNG := S4aux.hermitian_count_equality
/- English proof (translation)
The claim follows from `S4aux.shared_constant_formula`.
-/
theorem shared_constant_formula : Formalism.HermitianLatticeCounting.S4.LocalDensityShareBound := S4aux.shared_constant_formula
/- English proof (translation)
The claim follows from `S4aux.involution_map_linear`.
-/
theorem involution_map_linear : Formalism.HermitianLatticeCounting.S4.TauLin := S4aux.involution_map_linear
/- English proof (translation)
The claim follows from `S4aux.leakage_probability`.
-/
theorem leakage_probability : Formalism.HermitianLatticeCounting.S4.LeakProb := S4aux.leakage_probability
/- English proof (translation)
The claim follows from `S4aux.matrix_line_sums`.
-/
theorem matrix_line_sums : Formalism.HermitianLatticeCounting.S4.RowSums := S4aux.matrix_line_sums
/- English proof (translation)
The claim follows from `S4aux.self_dual_lattice_exists`.
-/
theorem self_dual_lattice_exists : Formalism.HermitianLatticeCounting.S4.BridgeExists := S4aux.self_dual_lattice_exists
/- English proof (translation)
The claim follows from `S4aux.self_dual_lattice_extension`.
-/
theorem self_dual_lattice_extension : Formalism.HermitianLatticeCounting.S4.BridgeSelfDual := S4aux.self_dual_lattice_extension
/- English proof (translation)
The claim follows from `S4aux.module_parts_decomposition`.
-/
theorem module_parts_decomposition : Formalism.HermitianLatticeCounting.S4.ThMParts := S4aux.module_parts_decomposition
/- English proof (translation)
The claim follows from `S4aux.involution_kernel`.
-/
theorem involution_kernel : Formalism.HermitianLatticeCounting.S4.TauKer := S4aux.involution_kernel
/- English proof (translation)
The claim follows from `S4aux.involution_map_hom`.
-/
theorem involution_map_hom : Formalism.HermitianLatticeCounting.S4.TauHom := S4aux.involution_map_hom
/- English proof (translation)
The claim follows from `S4aux.move_admissible`.
-/
theorem move_admissible : Formalism.HermitianLatticeCounting.S4.MoveAdm := S4aux.move_admissible
/- English proof (translation)
The claim follows from `S4aux.move_perpendicular_extended`.
-/
theorem move_perpendicular_extended : Formalism.HermitianLatticeCounting.S4.MovePerpX := S4aux.move_perpendicular_extended
/- English proof (translation)
The claim follows from `S4aux.dual_capacity_variant`.
-/
theorem dual_capacity_variant : Formalism.HermitianLatticeCounting.S4.DualCapV := S4aux.dual_capacity_variant
/- English proof (translation)
The claim follows from `S4aux.hermitian_count_assembly_of_type`.
-/
theorem hermitian_count_assembly_of_type : Formalism.HermitianLatticeCounting.S4.AssemblyNG2 := S4aux.hermitian_count_assembly_of_type
/- English proof (translation)
The claim follows from `S4aux.same_trace_hypothesis`.
-/
theorem same_trace_hypothesis : Formalism.HermitianLatticeCounting.S4.SameTraceHyp := S4aux.same_trace_hypothesis
/- English proof (translation)
The claim follows from `S4aux.conditional_count_formula`.
-/
theorem conditional_count_formula : Formalism.HermitianLatticeCounting.S4.CondCount := S4aux.conditional_count_formula
/- English proof (translation)
The claim follows from `S4aux.primitive_density_split_form`.
-/
theorem primitive_density_split_form : Formalism.HermitianLatticeCounting.S4.PrimDensitySplitForm := S4aux.primitive_density_split_form
/- English proof (translation)
The claim follows from `S4aux.primitive_density_split`.
-/
theorem primitive_density_split : Formalism.HermitianLatticeCounting.S4.PrimDensitySplit := S4aux.primitive_density_split
/- English proof (translation)
The claim follows from `S4aux.primitive_density_inert_form`.
-/
theorem primitive_density_inert_form : Formalism.HermitianLatticeCounting.S4.PrimDensityInertForm := S4aux.primitive_density_inert_form
/- English proof (translation)
The claim follows from `S4aux.primitive_density_inert`.
-/
theorem primitive_density_inert : Formalism.HermitianLatticeCounting.S4.PrimDensityInert := S4aux.primitive_density_inert
/- English proof (translation)
The claim follows from `S4aux.unimodular_rank`.
-/
theorem unimodular_rank : Formalism.HermitianLatticeCounting.S4.UnimodRank := S4aux.unimodular_rank
/- English proof (translation)
The claim follows from `S4aux.unimodular_hull`.
-/
theorem unimodular_hull : Formalism.HermitianLatticeCounting.S4.UnimodHull := S4aux.unimodular_hull
/- English proof (translation)
The claim follows from `S4aux.annihilator_size`.
-/
theorem annihilator_size : Formalism.HermitianLatticeCounting.S4.AnnihSize := S4aux.annihilator_size
/- English proof (translation)
The claim follows from `S4aux.hermitian_gauss_condition`.
-/
theorem hermitian_gauss_condition : Formalism.HermitianLatticeCounting.S4.HermGaussCond := S4aux.hermitian_gauss_condition
/- English proof (translation)
The claim follows from `S4aux.hermitian_standard_form`.
-/
theorem hermitian_standard_form : Formalism.HermitianLatticeCounting.S4.HermStdForm := S4aux.hermitian_standard_form
/- English proof (translation)
The claim follows from `S4aux.hermitian_jacobian`.
-/
theorem hermitian_jacobian : Formalism.HermitianLatticeCounting.S4.HermJac := S4aux.hermitian_jacobian

end Formalism.HermitianLatticeCounting.P
