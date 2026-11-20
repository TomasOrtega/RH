import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction

noncomputable section

open Finset

namespace PositivityTheory.RgBcC.RealD

open Formalism.REAL (GlRel)

variable {n : ℕ}

/- English proof (translation)
Introduce `a b hab`. Establish `h1 : (lam b : ℝ) ≤ lam a` using `by exact_mod_cast hlam hab.le`. Establish `h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast hab`. Simplify using `only [Lr]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lr_strictAnti {lam : Fin n → ℤ} (hlam : Antitone lam) : StrictAnti (Lr lam) := by
  intro a b hab
  have h1 : (lam b : ℝ) ≤ lam a := by exact_mod_cast hlam hab.le
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [Lr]
  linarith

section Intw

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : V →ₗ[ℂ] W)

def Intw (f : Module.End ℂ V) (g : Module.End ℂ W) : Prop := ∀ x, g (π x) = π (f x)

variable {π}

/- English proof (translation)
Introduce `x` and use `by simp [h x, h' x]`.
-/
theorem Intw.add {f f' g g'} (h : Intw π f g) (h' : Intw π f' g') : Intw π (f + f') (g + g') := fun x => by
  simp [h x, h' x]

/- English proof (translation)
Introduce `x` and use `by simp [h x, h' x]`.
-/
theorem Intw.sub {f f' g g'} (h : Intw π f g) (h' : Intw π f' g') : Intw π (f - f') (g - g') := fun x => by
  simp [h x, h' x]

/- English proof (translation)
Introduce `x` and use `by simp [h' x, h (f' x)]`.
-/
theorem Intw.mul {f f' g g'} (h : Intw π f g) (h' : Intw π f' g') : Intw π (f * f') (g * g') := fun x => by
  simp [h' x, h (f' x)]

/- English proof (translation)
Introduce `x` and use `by simp [h x]`.
-/
theorem Intw.smul {f g} (c : ℂ) (h : Intw π f g) : Intw π (c • f) (c • g) := fun x => by
  simp [h x]

/- English proof (translation)
Introduce `x` and use `by simp`.
-/
theorem Intw.zero : Intw π (0 : Module.End ℂ V) 0 := fun x => by simp

/- English proof (translation)
Introduce `x` and use `by simp [Module.algebraMap_end_apply]`.
-/
theorem Intw.algebraMap (c : ℂ) : Intw π (algebraMap ℂ (Module.End ℂ V) c) (algebraMap ℂ (Module.End ℂ W) c) :=
  fun x => by simp [Module.algebraMap_end_apply]

/- English proof (translation)
Use `Intw.algebraMap (π := π) (m : ℂ)` as an intermediate fact. Simplify using `using this`.
-/
theorem Intw.intCast (m : ℤ) : Intw π (m : Module.End ℂ V) (m : Module.End ℂ W) := by
  have := Intw.algebraMap (π := π) (m : ℂ)
  simpa using this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using Intw.zero`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `(h a).add ih`.
-/
theorem Intw.sum {ι : Type*} (s : Finset ι) {f : ι → Module.End ℂ V} {g : ι → Module.End ℂ W}
    (h : ∀ i, Intw π (f i) (g i)) : Intw π (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Intw.zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha]; exact (h a).add ih

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simpa using Intw.algebraMap (π := π) 1`. Consider the case `cons a l ih => simpa using (h a).mul ih`.
-/
theorem Intw.listMap {ι : Type*} (l : List ι) {f : ι → Module.End ℂ V} {g : ι → Module.End ℂ W}
    (h : ∀ i, Intw π (f i) (g i)) : Intw π (l.map f).prod (l.map g).prod := by
  induction l with
  | nil => simpa using Intw.algebraMap (π := π) 1
  | cons a l ih => simpa using (h a).mul ih

/- English proof (translation)
Use `Intw.listMap (List.finRange t) h` as an intermediate fact. Simplify `this` using `[List.ofFn_eq_map]`.
-/
theorem Intw.ofFn {t : ℕ} {f : Fin t → Module.End ℂ V} {g : Fin t → Module.End ℂ W} (h : ∀ i, Intw π (f i) (g i)) :
    Intw π (List.ofFn f).prod (List.ofFn g).prod := by
  have := Intw.listMap (List.finRange t) h
  simpa [List.ofFn_eq_map] using this

/- English proof (translation)
Proceed by induction on `z using FreeAlgebra.induction with`. Consider the case `grade0 r => simpa using Intw.algebraMap (π := π) r`. Consider the case `grade1 p => simpa using h p`. Consider the case `mul a b ha hb => simpa using ha.mul hb`. Consider the case `add a b ha hb => simpa using ha.add hb`.
-/
theorem Intw.lift {X : Type} {G : X → Module.End ℂ V} {G' : X → Module.End ℂ W} (h : ∀ p, Intw π (G p) (G' p))
    (z : FreeAlgebra ℂ X) : Intw π (FreeAlgebra.lift ℂ G z) (FreeAlgebra.lift ℂ G' z) := by
  induction z using FreeAlgebra.induction with
  | grade0 r => simpa using Intw.algebraMap (π := π) r
  | grade1 p => simpa using h p
  | mul a b ha hb => simpa using ha.mul hb
  | add a b ha hb => simpa using ha.add hb

/- English proof (translation)
Unfold `Formalism.REAL.qminor`. Use `Intw.sum _ fun σ => (Intw.intCast _).mul (Intw.ofFn fun k => ?_)` and prove the remaining obligations. Unfold `Formalism.REAL.Tm`. Use `Intw.add ?_ (h _ _)` and prove the remaining obligations. Use `split_ifs`.

Conclude with `Intw.algebraMap _`. Conclude with `Intw.zero`.
-/
theorem Intw.qminor {F : Fin n → Fin n → Module.End ℂ V} {G : Fin n → Fin n → Module.End ℂ W}
    (h : ∀ a b, Intw π (F a b) (G a b)) {t : ℕ} (r c : Fin t → Fin n) (u : ℂ) :
    Intw π (Formalism.REAL.qminor F r c u) (Formalism.REAL.qminor G r c u) := by
  unfold Formalism.REAL.qminor
  refine Intw.sum _ fun σ => (Intw.intCast _).mul (Intw.ofFn fun k => ?_)
  unfold Formalism.REAL.Tm
  refine Intw.add ?_ (h _ _)
  split_ifs
  · exact Intw.algebraMap _
  · exact Intw.zero

/- English proof (translation)
The claim follows from `Intw.qminor h _ _ _`.
-/
theorem Intw.capS {F : Fin n → Fin n → Module.End ℂ V} {G : Fin n → Fin n → Module.End ℂ W}
    (h : ∀ a b, Intw π (F a b) (G a b)) (lev : Fin n → ℕ) (j : ℕ) (u : ℂ) : Intw π (capS F lev j u) (capS G lev j u) :=
  Intw.qminor h _ _ _

/- English proof (translation)
Proceed by induction on `z using FreeAlgebra.induction with`. Consider the case `grade0 r => simpa using Intw.algebraMap (π := π) r`. Consider the case `grade1 p => exact h p`. Consider the case `mul a b ha hb => simpa using ha.mul hb`. Consider the case `add a b ha hb => simpa using ha.add hb`.
-/
theorem Intw.algHom {X : Type} (φ : FreeAlgebra ℂ X →ₐ[ℂ] Module.End ℂ V) (ψ : FreeAlgebra ℂ X →ₐ[ℂ] Module.End ℂ W)
    (h : ∀ p, Intw π (φ (FreeAlgebra.ι ℂ p)) (ψ (FreeAlgebra.ι ℂ p))) (z : FreeAlgebra ℂ X) : Intw π (φ z) (ψ z) := by
  induction z using FreeAlgebra.induction with
  | grade0 r => simpa using Intw.algebraMap (π := π) r
  | grade1 p => exact h p
  | mul a b ha hb => simpa using ha.mul hb
  | add a b ha hb => simpa using ha.add hb

/- English proof (translation)
The claim follows from `LinearMap.ext fun y => by obtain ⟨x, rfl⟩ := hs y rw [h, h', e]`.
-/
theorem Intw.eq {f f' : Module.End ℂ V} {g g' : Module.End ℂ W} (h : Intw π f g) (h' : Intw π f' g')
    (hs : Function.Surjective π) (e : f = f') : g = g' :=
  LinearMap.ext fun y => by
    obtain ⟨x, rfl⟩ := hs y
    rw [h, h', e]

end Intw

def qOp {V : Type} [AddCommGroup V] [Module ℂ V] (B : Submodule ℂ V) (f : Module.End ℂ V) : Module.End ℂ (V ⧸ B) :=
  open Classical in if h : B ≤ B.comap f then B.mapQ B f h else 0

/- English proof (translation)
Introduce `x` and use `by unfold qOp rw [dif_pos (show B ≤ B.comap f from fun y hy => h y hy)] rfl`.
-/
theorem qOp_intw {V : Type} [AddCommGroup V] [Module ℂ V] (B : Submodule ℂ V) (f : Module.End ℂ V)
    (h : ∀ x ∈ B, f x ∈ B) : Intw B.mkQ f (qOp B f) := fun x => by
  unfold qOp
  rw [dif_pos (show B ≤ B.comap f from fun y hy => h y hy)]
  rfl

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Simplify using `only [firstLeviFamily, secondLeviFamily]`. Use `module`.
-/
theorem first_add_second_levi_family (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) :
    firstLeviFamily lev E1 E2 p q + secondLeviFamily lev E1 E2 p q = evLc lev E1 E2 (FreeAlgebra.ι ℂ (false, p, q)) := by
  simp only [firstLeviFamily, secondLeviFamily]
  module

/- English proof (translation)
Simplify using `only [firstLeviFamily, secondLeviFamily]`. Use `module`.
-/
theorem first_sub_second_levi_family (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) :
    firstLeviFamily lev E1 E2 p q - secondLeviFamily lev E1 E2 p q = evLc lev E1 E2 (FreeAlgebra.ι ℂ (true, p, q)) := by
  simp only [firstLeviFamily, secondLeviFamily]
  module

/- English proof (translation)
Distinguish the cases in `h : lev p = lev q`. Conclude with `⟨fun x hx => (hLS n lev hmono V E1 E2 hp p q h x hx).1, fun x hx => (hLS n lev hmono V E1 E2 hp p q h x hx).2⟩`. Establish `h1 : firstLeviFamily lev E1 E2 p q = 0` using `by simp [firstLeviFamily, evLc, h]`. Establish `h2 : secondLeviFamily lev E1 E2 p q = 0` using `by simp [secondLeviFamily, evLc, h]`. Conclude with `⟨fun x _ => by simp [h1], fun x _ => by simp [h2]⟩`.
-/
theorem fc_stab (hLS : LevStab) {lev : Fin n → ℕ} (hmono : Monotone lev) {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (hp : IsPairA E1 E2) (p q : Fin n) :
    (∀ x ∈ bdSub lev E1 E2, firstLeviFamily lev E1 E2 p q x ∈ bdSub lev E1 E2) ∧
      ∀ x ∈ bdSub lev E1 E2, secondLeviFamily lev E1 E2 p q x ∈ bdSub lev E1 E2 := by
  by_cases h : lev p = lev q
  · exact ⟨fun x hx => (hLS n lev hmono V E1 E2 hp p q h x hx).1, fun x hx => (hLS n lev hmono V E1 E2 hp p q h x hx).2⟩
  · have h1 : firstLeviFamily lev E1 E2 p q = 0 := by simp [firstLeviFamily, evLc, h]
    have h2 : secondLeviFamily lev E1 E2 p q = 0 := by simp [secondLeviFamily, evLc, h]
    exact ⟨fun x _ => by simp [h1], fun x _ => by simp [h2]⟩

end Chains

/- English proof (translation)
Introduce `hP hI hH hA hLS hLR hSC hCC h4 h5`. Introduce `n lam hlam lev hlev V _ _ E1 E2 hadm v w hv hw hv0 hx`. Establish `hp : IsPairA E1 E2` using `⟨hadm.gl1, hadm.gl2, hadm.comm⟩`. Take `⟨a, ha, hav⟩` from `hP n lam lev V E1 E2 hadm _ v w hv hw hv0 hx`. Take `⟨b, hb, hcong⟩` from `hH n lev hlev.1 a ha`.

Take `⟨σ1, σ2, hsh, hcap⟩` from `hCC n lam hlam lev hlev`. Set `B : Submodule ℂ (Cq n V)` to `bdSub lev E1 E2`. Set `FrobeniusMapsXPow : Fin n → Fin n → Module.End ℂ (Cq n V ⧸ B)` to `fun p q => qOp B (firstLeviFamily lev E1 E2 p q)`. Set `FiniteCocycleOfIntegral : Fin n → Fin n → Module.End ℂ (Cq n V ⧸ B)` to `fun p q => qOp B (secondLeviFamily lev E1 E2 p q)`. Establish `i1 : ∀ p q, Intw B.mkQ (firstLeviFamily lev E1 E2 p q) (FrobeniusMapsXPow p q)` using `fun p q => qOp_intw B _ (fc_stab hLS hlev.1 hp p q).1`.

Establish `i2 : ∀ p q, Intw B.mkQ (secondLeviFamily lev E1 E2 p q) (FiniteCocycleOfIntegral p q)` using `fun p q => qOp_intw B _ (fc_stab hLS hlev.1 hp p q).2`. Establish `hsurj : Function.Surjective B.mkQ` using `B.mkQ_surjective`. Establish `hLq : IsLevPairA lev FrobeniusMapsXPow FiniteCocycleOfIntegral`. Introduce `p q r s h1 h2`. Take `⟨r1, r2, r3⟩` from `hLR n lev hlev.1 V E1 E2 hp p q r s h1 h2`.

Establish `ite1 : ∀ (c : Prop) [Decidable c] (x y : Fin n), Intw B.mkQ (if c then firstLeviFamily lev E1 E2 x y else 0) (if c then FrobeniusMapsXPow x y else 0)` using `fun c _ x y => by split_ifs`. Conclude with `i1 x y`. Conclude with `Intw.zero`. Establish `ite2 : ∀ (c : Prop) [Decidable c] (x y : Fin n), Intw B.mkQ (if c then secondLeviFamily lev E1 E2 x y else 0) (if c then FiniteCocycleOfIntegral x y else 0)` using `fun c _ x y => by split_ifs`. Conclude with `i2 x y`.

Conclude with `Intw.zero`. Conclude with `⟨Intw.eq (((i1 p q).mul (i1 r s)).sub ((i1 r s).mul (i1 p q))) ((ite1 _ p s).sub (ite1 _ r q)) hsurj r1, Intw.eq (((i2 p q).mul (i2 r s)).sub ((i2 r s).mul (i2 p q))) ((ite2 _ p s).sub (ite2 _ r q)) hsurj r2, Intw.eq ((i1 p q).mul (i2 r s)) ((i2 r s).mul (i1 p q)) hsurj r3⟩`. Set `ν : Fin n → ℝ` to `fun a => muQ lam lev a + 2 * rhoU lev a`. Establish `hcent : ∀ a c, lev a = lev c → ν a = ν c`. Introduce `a c h`.

Simplify using `only [ν, muQ, rhoU, h, hlev.2 a c h]`. Set `c : Cq n V ⧸ B` to `B.mkQ (Pi.single (omU lev) v : Cq n V)`. Establish `hsemi : ∀ a' c', lev a' = lev c' → (FrobeniusMapsXPow a' c' + FiniteCocycleOfIntegral a' c') c = if a' = c' then (ν a' : ℂ) • c else 0`. Introduce `a' c' h`. Rewrite using `[((i1 a' c').add (i2 a' c')) _, hSC n lam hlam lev hlev V E1 E2 hadm v hv a' c' h]`.

Apply the tactic sequence `split_ifs <;> simp [c, ν]`. Establish `hcap1 : ∀ u : ℂ, capProd FrobeniusMapsXPow lev σ1 u c = (∏ a, (u + (Lr lam a : ℂ))) • c`. Introduce `u`. Establish `hi` using `Intw.listMap (π := B.mkQ) (levs lev) (fun j => Intw.capS i1 lev j (u - σ1 j))`. Simplify using `only [capProd, c]`.

Rewrite using `[hi, ← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `(hcap V E1 E2 hadm v hv u).1`. Establish `hcap2 : ∀ u : ℂ, capProd FiniteCocycleOfIntegral lev σ2 u c = (∏ a, (u + (Lr lam a : ℂ))) • c`. Introduce `u`. Establish `hi` using `Intw.listMap (π := B.mkQ) (levs lev) (fun j => Intw.capS i2 lev j (u - σ2 j))`.

Simplify using `only [capProd, c]`. Rewrite using `[hi, ← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `(hcap V E1 E2 hadm v hv u).2`. Establish `hS5` using `h5 n (Lr lam) (lr_strictAnti hlam) lev hlev.1 ν σ1 σ2 hsh (Cq n V ⧸ B) FrobeniusMapsXPow FiniteCocycleOfIntegral hLq c hsemi hcap1 hcap2`. Take `⟨z, hz⟩` from `h4 n lev hlev.1 b hb ν hcent`.

Set `sc : ℕ × ℂ → ℂ` to `fun p => ∏ a ∈ blk lev p.1, (p.2 + σ1 p.1 + (Lr lam a : ℂ))`. Establish `hev : ∀ z : FreeAlgebra ℂ (ℕ × ℂ), evCap lev FrobeniusMapsXPow z c = FreeAlgebra.lift ℂ sc z • c`. Introduce `z`. Proceed by induction on `z using FreeAlgebra.induction with`. Consider the case `grade0 r => simp [Module.algebraMap_end_apply]`.

Consider the case `grade1 p => simp [evCap, sc, hS5 p.1 p.2]`. Consider the case `mul x y hx hy => rw [map_mul, map_mul, Module.End.mul_apply, hy, map_smul, hx, smul_smul, mul_comm]`. Consider the case `add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, add_smul]`. Establish `hkill : ∀ l : Lt n, l.1 = false → inUU lev l → xL E1 E2 l v = 0`. Introduce `l hl _`.

Establish `hlt : l.2.1.1 < l.2.1.2` using `l.2.2`. Simplify using `only [xL, hl, Bool.false_eq_true, if_false]`. Conclude with `hv.2 _ _ hlt rfl`. Take `⟨y, hyS, hyD, hyEq⟩` from `hA n lev hlev.1 a b ha hcong V E1 E2 hp v hkill`. Establish `iL : Intw B.mkQ (evLc lev E1 E2 b) (evLv lev FrobeniusMapsXPow FiniteCocycleOfIntegral b)`.

Use `Intw.algHom _ _ (fun p => ?_) b` and prove the remaining obligations. Take `⟨s, p1, p2⟩` from `p`. Distinguish the cases in `h : lev p1 = lev p2`. Consider the cases of `s`. Establish `e : evLv lev FrobeniusMapsXPow FiniteCocycleOfIntegral (FreeAlgebra.ι ℂ (false, p1, p2)) = FrobeniusMapsXPow p1 p2 + FiniteCocycleOfIntegral p1 p2`.

Simplify using `[evLv, h, kA]`. Rewrite using `[e, ← first_add_second_levi_family]`. Conclude with `(i1 p1 p2).add (i2 p1 p2)`. Establish `e : evLv lev FrobeniusMapsXPow FiniteCocycleOfIntegral (FreeAlgebra.ι ℂ (true, p1, p2)) = FrobeniusMapsXPow p1 p2 - FiniteCocycleOfIntegral p1 p2`. Simplify using `[evLv, h, pA]`.

Rewrite using `[e, ← first_sub_second_levi_family]`. Conclude with `(i1 p1 p2).sub (i2 p1 p2)`. Establish `e1 : evLc lev E1 E2 (FreeAlgebra.ι ℂ (s, p1, p2)) = 0` using `by simp [evLc, h]`. Establish `e2 : evLv lev FrobeniusMapsXPow FiniteCocycleOfIntegral (FreeAlgebra.ι ℂ (s, p1, p2)) = 0` using `by simp [evLv, h]`. Rewrite using `[e1, e2]`.

Conclude with `Intw.zero`. Establish `hbd : bdL (inUU lev) E1 E2 y ∈ B` using `Submodule.mem_map.2 ⟨y, ⟨hyS, hyD⟩, rfl⟩`. Establish `hcw : B.mkQ (Pi.single (omU lev) w : Cq n V) = FreeAlgebra.lift ℂ sc z • c`. Establish `e1 : B.mkQ (Pi.single (omU lev) (evKP E1 E2 a v) - evLc lev E1 E2 b (Pi.single (omU lev) v) : Cq n V) = 0`. Rewrite using `[hyEq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Conclude with `hbd`. Rewrite `e1` using `[map_sub, sub_eq_zero, ← iL]`. Rewrite using `[← hav, e1, hz (Cq n V ⧸ B) FrobeniusMapsXPow FiniteCocycleOfIntegral hLq c hsemi, hev z]`. Use `⟨FreeAlgebra.lift ℂ sc z, ?_⟩` and prove the remaining obligations. Establish `hmem : w - FreeAlgebra.lift ℂ sc z • v ∈ hwSp E1 E2 (muQ lam lev)` using `sub_mem hw (Submodule.smul_mem _ _ hv)`.

Establish `hzero : (Pi.single (omU lev) (w - FreeAlgebra.lift ℂ sc z • v) : Cq n V) ∈ B`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, Pi.single_sub, Pi.single_smul, map_sub, map_smul, hcw]`. Simplify using `[c]`. Take `⟨y', ⟨hy'S, hy'D⟩, hy'⟩` from `Submodule.mem_map.1 hzero`. Conclude with `sub_eq_zero.1 (hI n lam hlam lev hlev V E1 E2 hadm _ y' hmem hy'S hy'D hy')`.
-/
theorem multiplicity_assembly_holds : MultiplicityAssembly := by
  intro hP hI hH hA hLS hLR hSC hCC h4 h5
  intro n lam hlam lev hlev V _ _ E1 E2 hadm v w hv hw hv0 hx
  have hp : IsPairA E1 E2 := ⟨hadm.gl1, hadm.gl2, hadm.comm⟩
  obtain ⟨a, ha, hav⟩ := hP n lam lev V E1 E2 hadm _ v w hv hw hv0 hx
  obtain ⟨b, hb, hcong⟩ := hH n lev hlev.1 a ha
  obtain ⟨σ1, σ2, hsh, hcap⟩ := hCC n lam hlam lev hlev
  let B : Submodule ℂ (Cq n V) := bdSub lev E1 E2
  let FrobeniusMapsXPow : Fin n → Fin n → Module.End ℂ (Cq n V ⧸ B) := fun p q => qOp B (firstLeviFamily lev E1 E2 p q)
  let FiniteCocycleOfIntegral : Fin n → Fin n → Module.End ℂ (Cq n V ⧸ B) := fun p q => qOp B (secondLeviFamily lev E1 E2 p q)
  have i1 : ∀ p q, Intw B.mkQ (firstLeviFamily lev E1 E2 p q) (FrobeniusMapsXPow p q) := fun p q =>
    qOp_intw B _ (fc_stab hLS hlev.1 hp p q).1
  have i2 : ∀ p q, Intw B.mkQ (secondLeviFamily lev E1 E2 p q) (FiniteCocycleOfIntegral p q) := fun p q =>
    qOp_intw B _ (fc_stab hLS hlev.1 hp p q).2
  have hsurj : Function.Surjective B.mkQ := B.mkQ_surjective
  have hLq : IsLevPairA lev FrobeniusMapsXPow FiniteCocycleOfIntegral := by
    intro p q r s h1 h2
    obtain ⟨r1, r2, r3⟩ := hLR n lev hlev.1 V E1 E2 hp p q r s h1 h2
    have ite1 : ∀ (c : Prop) [Decidable c] (x y : Fin n),
        Intw B.mkQ (if c then firstLeviFamily lev E1 E2 x y else 0) (if c then FrobeniusMapsXPow x y else 0) := fun c _ x y => by
      split_ifs
      · exact i1 x y
      · exact Intw.zero
    have ite2 : ∀ (c : Prop) [Decidable c] (x y : Fin n),
        Intw B.mkQ (if c then secondLeviFamily lev E1 E2 x y else 0) (if c then FiniteCocycleOfIntegral x y else 0) := fun c _ x y => by
      split_ifs
      · exact i2 x y
      · exact Intw.zero
    exact ⟨Intw.eq (((i1 p q).mul (i1 r s)).sub ((i1 r s).mul (i1 p q))) ((ite1 _ p s).sub (ite1 _ r q)) hsurj r1,
      Intw.eq (((i2 p q).mul (i2 r s)).sub ((i2 r s).mul (i2 p q))) ((ite2 _ p s).sub (ite2 _ r q)) hsurj r2,
      Intw.eq ((i1 p q).mul (i2 r s)) ((i2 r s).mul (i1 p q)) hsurj r3⟩
  let ν : Fin n → ℝ := fun a => muQ lam lev a + 2 * rhoU lev a
  have hcent : ∀ a c, lev a = lev c → ν a = ν c := by
    intro a c h
    simp only [ν, muQ, rhoU, h, hlev.2 a c h]
  let c : Cq n V ⧸ B := B.mkQ (Pi.single (omU lev) v : Cq n V)
  have hsemi : ∀ a' c', lev a' = lev c' → (FrobeniusMapsXPow a' c' + FiniteCocycleOfIntegral a' c') c = if a' = c' then (ν a' : ℂ) • c else 0 := by
    intro a' c' h
    rw [((i1 a' c').add (i2 a' c')) _, hSC n lam hlam lev hlev V E1 E2 hadm v hv a' c' h]
    split_ifs <;> simp [c, ν]
  have hcap1 : ∀ u : ℂ, capProd FrobeniusMapsXPow lev σ1 u c = (∏ a, (u + (Lr lam a : ℂ))) • c := by
    intro u
    have hi := Intw.listMap (π := B.mkQ) (levs lev) (fun j => Intw.capS i1 lev j (u - σ1 j))
    simp only [capProd, c]
    rw [hi, ← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (hcap V E1 E2 hadm v hv u).1
  have hcap2 : ∀ u : ℂ, capProd FiniteCocycleOfIntegral lev σ2 u c = (∏ a, (u + (Lr lam a : ℂ))) • c := by
    intro u
    have hi := Intw.listMap (π := B.mkQ) (levs lev) (fun j => Intw.capS i2 lev j (u - σ2 j))
    simp only [capProd, c]
    rw [hi, ← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (hcap V E1 E2 hadm v hv u).2
  have hS5 := h5 n (Lr lam) (lr_strictAnti hlam) lev hlev.1 ν σ1 σ2 hsh (Cq n V ⧸ B) FrobeniusMapsXPow FiniteCocycleOfIntegral hLq c hsemi hcap1 hcap2
  obtain ⟨z, hz⟩ := h4 n lev hlev.1 b hb ν hcent
  let sc : ℕ × ℂ → ℂ := fun p => ∏ a ∈ blk lev p.1, (p.2 + σ1 p.1 + (Lr lam a : ℂ))
  have hev : ∀ z : FreeAlgebra ℂ (ℕ × ℂ), evCap lev FrobeniusMapsXPow z c = FreeAlgebra.lift ℂ sc z • c := by
    intro z
    induction z using FreeAlgebra.induction with
    | grade0 r => simp [Module.algebraMap_end_apply]
    | grade1 p => simp [evCap, sc, hS5 p.1 p.2]
    | mul x y hx hy => rw [map_mul, map_mul, Module.End.mul_apply, hy, map_smul, hx, smul_smul, mul_comm]
    | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, add_smul]
  have hkill : ∀ l : Lt n, l.1 = false → inUU lev l → xL E1 E2 l v = 0 := by
    intro l hl _
    have hlt : l.2.1.1 < l.2.1.2 := l.2.2
    simp only [xL, hl, Bool.false_eq_true, if_false]
    exact hv.2 _ _ hlt rfl
  obtain ⟨y, hyS, hyD, hyEq⟩ := hA n lev hlev.1 a b ha hcong V E1 E2 hp v hkill
  have iL : Intw B.mkQ (evLc lev E1 E2 b) (evLv lev FrobeniusMapsXPow FiniteCocycleOfIntegral b) := by
    refine Intw.algHom _ _ (fun p => ?_) b
    obtain ⟨s, p1, p2⟩ := p
    by_cases h : lev p1 = lev p2
    · cases s
      · have e : evLv lev FrobeniusMapsXPow FiniteCocycleOfIntegral (FreeAlgebra.ι ℂ (false, p1, p2)) = FrobeniusMapsXPow p1 p2 + FiniteCocycleOfIntegral p1 p2 := by
          simp [evLv, h, kA]
        rw [e, ← first_add_second_levi_family]
        exact (i1 p1 p2).add (i2 p1 p2)
      · have e : evLv lev FrobeniusMapsXPow FiniteCocycleOfIntegral (FreeAlgebra.ι ℂ (true, p1, p2)) = FrobeniusMapsXPow p1 p2 - FiniteCocycleOfIntegral p1 p2 := by
          simp [evLv, h, pA]
        rw [e, ← first_sub_second_levi_family]
        exact (i1 p1 p2).sub (i2 p1 p2)
    · have e1 : evLc lev E1 E2 (FreeAlgebra.ι ℂ (s, p1, p2)) = 0 := by simp [evLc, h]
      have e2 : evLv lev FrobeniusMapsXPow FiniteCocycleOfIntegral (FreeAlgebra.ι ℂ (s, p1, p2)) = 0 := by simp [evLv, h]
      rw [e1, e2]
      exact Intw.zero
  have hbd : bdL (inUU lev) E1 E2 y ∈ B := Submodule.mem_map.2 ⟨y, ⟨hyS, hyD⟩, rfl⟩
  have hcw : B.mkQ (Pi.single (omU lev) w : Cq n V) = FreeAlgebra.lift ℂ sc z • c := by
    have e1 : B.mkQ (Pi.single (omU lev) (evKP E1 E2 a v) - evLc lev E1 E2 b (Pi.single (omU lev) v) : Cq n V) = 0 := by
      rw [hyEq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hbd
    rw [map_sub, sub_eq_zero, ← iL] at e1
    rw [← hav, e1, hz (Cq n V ⧸ B) FrobeniusMapsXPow FiniteCocycleOfIntegral hLq c hsemi, hev z]
  refine ⟨FreeAlgebra.lift ℂ sc z, ?_⟩
  have hmem : w - FreeAlgebra.lift ℂ sc z • v ∈ hwSp E1 E2 (muQ lam lev) := sub_mem hw (Submodule.smul_mem _ _ hv)
  have hzero : (Pi.single (omU lev) (w - FreeAlgebra.lift ℂ sc z • v) : Cq n V) ∈ B := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, Pi.single_sub, Pi.single_smul, map_sub, map_smul, hcw]
    simp [c]
  obtain ⟨y', ⟨hy'S, hy'D⟩, hy'⟩ := Submodule.mem_map.1 hzero
  exact sub_eq_zero.1 (hI n lam hlam lev hlev V E1 E2 hadm _ y' hmem hy'S hy'D hy')

end PositivityTheory.RgBcC.RealD
