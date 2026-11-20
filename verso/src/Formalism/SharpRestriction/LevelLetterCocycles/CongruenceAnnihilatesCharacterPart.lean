import Formalism.SharpRestriction.LevelLetterCocycles.TypePrimeCongruences
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InSpanAdd

noncomputable section

namespace Formalism.MainNotions.TypePrimeCongruences.CongruenceModules

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section Span

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  {X' : Type} (T' : Subalgebra (N.O i) (X' → N.O i)) (rep : X' → (GE N →* MatN N i))

/- English proof (translation)
Use `⟨1, fun _ => f, fun _ => 1, fun _ => hf, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x'`. Simplify using the standard rewrite rules.
-/
theorem inSpan_scal (f : X' → N.O i) (hf : f ∈ T') :
    InSpan N i T' rep (fun x' => f x' • (1 : MatN N i)) := by
  refine ⟨1, fun _ => f, fun _ => 1, fun _ => hf, ?_⟩
  funext x'
  simp

/- English proof (translation)
Use `inSpan_scal N T' rep 1 T'.one_mem` as an intermediate fact. Simplify using `only [Pi.one_apply, one_smul] at this`. Conclude with `this`.
-/
theorem inSpan_one : InSpan N i T' rep 1 := by
  have := inSpan_scal N T' rep 1 T'.one_mem
  simp only [Pi.one_apply, one_smul] at this
  exact this

/- English proof (translation)
Apply the tactic sequence `first | exact UpperTheory.Reformulated.B.Qj25.inSpan_add .. | (apply UpperTheory.Reformulated.B.Qj25.inSpan_add <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qj25.inSpan_add <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj25.inSpan_add <;> assumption) | (intr …`.
-/
theorem inSpan_add {a b : X' → MatN N i} (ha : InSpan N i T' rep a) (hb : InSpan N i T' rep b) :
    InSpan N i T' rep (a + b) := by
  first | exact UpperTheory.Reformulated.B.Qj25.inSpan_add .. | (apply UpperTheory.Reformulated.B.Qj25.inSpan_add <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qj25.inSpan_add <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj25.inSpan_add <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qj25.inSpan_add <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj25.inSpan_add <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qj25.inSpan_add R H what₂ N i X' T' rep a b ha hb | exact @UpperTheory.Reformulated.B.Qj25.inSpan_add R H what₂ N i X' T' rep a b ha | exact @UpperTheory.Reformulated.B.Qj25.inSpan_add R H what₂ N i X' T' rep a b | exact @UpperTheory.Reformulated.B.Qj25.inSpan_add R H what₂ N i X' T' rep a | exact @UpperTheory.Reformulated.B.Qj25.inSpan_add R H what₂ N i X' T' rep | exact @UpperTheory.Reformulated.B.Qj25.inSpan_add R H what₂ N i X' T' | exact @UpperTheory.Reformulated.B.Qj25.inSpan_add R H what₂ N i X' | exact @UpperTheory.Reformulated.B.Qj25.inSpan_add R H what₂ N i | exact @UpperTheory.Reformulated.B.Qj25.inSpan_add R H what₂ N | exact @UpperTheory.Reformulated.B.Qj25.inSpan_add R H what₂ | exact @UpperTheory.Reformulated.B.Qj25.inSpan_add R H | exact @UpperTheory.Reformulated.B.Qj25.inSpan_add R

/- English proof (translation)
Take `⟨m, f', g, hf', rfl⟩` from `ha`. Use `⟨m, fun k => f * f' k, g, fun k => T'.mul_mem hf (hf' k), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x'`. Simplify using `[Finset.smul_sum, mul_smul]`.
-/
theorem inSpan_fmul {a : X' → MatN N i} (f : X' → N.O i) (hf : f ∈ T') (ha : InSpan N i T' rep a) :
    InSpan N i T' rep (fun x' => f x' • a x') := by
  obtain ⟨m, f', g, hf', rfl⟩ := ha
  refine ⟨m, fun k => f * f' k, g, fun k => T'.mul_mem hf (hf' k), ?_⟩
  funext x'
  simp [Finset.smul_sum, mul_smul]

/- English proof (translation)
Take `⟨m, f, g, hf, rfl⟩` from `ha`. Take `⟨m', f', g', hf', rfl⟩` from `hb`. Set `e : Fin m × Fin m' ≃ Fin (m * m')` to `finProdFinEquiv`. Use `⟨m * m', fun q => f (e.symm q).1 * f' (e.symm q).2, fun q => g (e.symm q).1 * g' (e.symm q).2, fun q => T'.mul_mem (hf _) (hf' _), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_mul_sum, ← Fintype.sum_prod_type']`.

Use `Fintype.sum_equiv e _ _ (fun x => ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `x'`. Simplify using `only [Equiv.symm_apply_apply, Pi.mul_apply, map_mul]`. Rewrite using `[smul_mul_smul_comm]`.
-/
theorem inSpan_mul {a b : X' → MatN N i} (ha : InSpan N i T' rep a) (hb : InSpan N i T' rep b) :
    InSpan N i T' rep (a * b) := by
  obtain ⟨m, f, g, hf, rfl⟩ := ha
  obtain ⟨m', f', g', hf', rfl⟩ := hb
  let e : Fin m × Fin m' ≃ Fin (m * m') := finProdFinEquiv
  refine ⟨m * m', fun q => f (e.symm q).1 * f' (e.symm q).2, fun q => g (e.symm q).1 * g' (e.symm q).2,
    fun q => T'.mul_mem (hf _) (hf' _), ?_⟩
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv e _ _ (fun x => ?_)
  funext x'
  simp only [Equiv.symm_apply_apply, Pi.mul_apply, map_mul]
  rw [smul_mul_smul_comm]

end Span

section Block

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}

/- English proof (translation)
Use extensionality with `a b`. Use `congrFun (h (Pi.single b 1)) a` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.map_apply]`.
-/
theorem mat_eq_of_mulVec {n : ℕ} (A B : Matrix (Fin n) (Fin n) (N.O i))
    (h : ∀ v, (A.map (toK N i)).mulVec v = (B.map (toK N i)).mulVec v) : A = B := by
  ext a b
  have := congrFun (h (Pi.single b 1)) a
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.map_apply] using this

/- English proof (translation)
Establish `hm : (∑ k, c k • M k).map (toK N i) = ∑ k, toK N i (c k) • (M k).map (toK N i)`. Use extensionality with `a b`. Simplify using `only [Matrix.sum_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul]`. Rewrite using `[hm, Matrix.sum_mulVec]`. Simplify using `only [Matrix.smul_mulVec]`.
-/
theorem mapSum_mulVec {n m : ℕ} (c : Fin m → N.O i) (M : Fin m → Matrix (Fin n) (Fin n) (N.O i))
    (v : Fin n → KK N i) :
    ((∑ k, c k • M k).map (toK N i)).mulVec v = ∑ k, toK N i (c k) • ((M k).map (toK N i)).mulVec v := by
  have hm : (∑ k, c k • M k).map (toK N i) = ∑ k, toK N i (c k) • (M k).map (toK N i) := by
    ext a b
    simp only [Matrix.sum_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul]
  rw [hm, Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec]

variable (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))
  (π : N.X i) (S : IdempotentChoiceData N i)

/- English proof (translation)
Take `⟨-, hdec, hR', -, -, -, -, -, -, ⟨hpπ, -⟩, -, -⟩` from `hG`. Use `set a : S.X' → MatN N i := ∑ k, fun x' => f k x' • rO N i r (S.p x') (g k) with ha`. Establish `hIn : InR' N r S a` using `⟨m, f, g, hf, rfl⟩`. Establish `h1` using `hR' a hIn`. Establish `hval : a S.π' = ∑ k, f k S.π' • rO N i r π (g k)`.

Rewrite using `[ha, Finset.sum_apply, hpπ]`. Establish `hdec' : ∀ g u, S.e (((rO N i r π g).map (toK N i)).mulVec u) = (((rhoO N i ρ π g).map (toK N i)).mulVec (S.e u).1, fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (S.e u).2 c)` using `hdec`. Establish `key : ∀ u, S.e (((a S.π').map (toK N i)).mulVec u) = ∑ k, toK N i (f k S.π') • (((rhoO N i ρ π (g k)).map (toK N i)).mulVec (S.e u).1, fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) (g k) : (N.O i)ˣ) : N.O i) * (S.e u).2 c)`. Introduce `u`. Rewrite using `[hval, mapSum_mulVec, map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hdec']`. Prove the components needed by the constructor for the conclusion. Apply `mat_eq_of_mulVec` to reduce the goal to its premises. Introduce `v`.

Establish `h2` using `congrArg Prod.fst ((h1 (S.e.symm (v, 0))).symm.trans (key _))`. Simplify using `only [LinearEquiv.apply_symm_apply, Prod.fst_sum, Prod.smul_fst] at h2`. Rewrite using `[h2, mapSum_mulVec]`. Introduce `c`. Establish `h2` using `congrFun (congrArg Prod.snd ((h1 (S.e.symm (0, Pi.single c 1))).symm.trans (key _))) c`.

Simplify using `only [LinearEquiv.apply_symm_apply, Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same, mul_one, smul_eq_mul] at h2`. Apply `IsFractionRing.injective (N.O i) (KK N i)` to reduce the goal to its premises. Rewrite using `[h2, map_sum]`. Simplify using `[map_mul]`.
-/
theorem psi_sum (hG : GoodCongruenceObjects N r ρ π S) (m : ℕ) (f : Fin m → S.X' → N.O i) (g : Fin m → GE N)
    (hf : ∀ k, f k ∈ S.T') :
    S.ψρ (∑ k, fun x' => f k x' • rO N i r (S.p x') (g k)) = ∑ k, f k S.π' • rhoO N i ρ π (g k) ∧
    ∀ c : Fin R.t, S.ψχ c (∑ k, fun x' => f k x' • rO N i r (S.p x') (g k)) =
      ∑ k, f k S.π' * ((chiU N i ((c : ℕ) + 1) (g k) : (N.O i)ˣ) : N.O i) := by
  obtain ⟨-, hdec, hR', -, -, -, -, -, -, ⟨hpπ, -⟩, -, -⟩ := hG
  set a : S.X' → MatN N i := ∑ k, fun x' => f k x' • rO N i r (S.p x') (g k) with ha
  have hIn : InR' N r S a := ⟨m, f, g, hf, rfl⟩
  have h1 := hR' a hIn
  have hval : a S.π' = ∑ k, f k S.π' • rO N i r π (g k) := by
    rw [ha, Finset.sum_apply, hpπ]
  have hdec' : ∀ g u, S.e (((rO N i r π g).map (toK N i)).mulVec u) =
      (((rhoO N i ρ π g).map (toK N i)).mulVec (S.e u).1,
        fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (S.e u).2 c) :=
    hdec
  have key : ∀ u, S.e (((a S.π').map (toK N i)).mulVec u) =
      ∑ k, toK N i (f k S.π') • (((rhoO N i ρ π (g k)).map (toK N i)).mulVec (S.e u).1,
        fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) (g k) : (N.O i)ˣ) : N.O i) * (S.e u).2 c) := by
    intro u
    rw [hval, mapSum_mulVec, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hdec']
  constructor
  · apply mat_eq_of_mulVec
    intro v
    have h2 := congrArg Prod.fst ((h1 (S.e.symm (v, 0))).symm.trans (key _))
    simp only [LinearEquiv.apply_symm_apply, Prod.fst_sum, Prod.smul_fst] at h2
    rw [h2, mapSum_mulVec]
  · intro c
    have h2 := congrFun (congrArg Prod.snd ((h1 (S.e.symm (0, Pi.single c 1))).symm.trans (key _))) c
    simp only [LinearEquiv.apply_symm_apply, Prod.snd_sum, Prod.smul_snd, Finset.sum_apply,
      Pi.smul_apply, Pi.single_eq_same, mul_one, smul_eq_mul] at h2
    apply IsFractionRing.injective (N.O i) (KK N i)
    rw [h2, map_sum]
    simp [map_mul]

end Block

section Main

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))
  (π : N.X i) (S : IdempotentChoiceData N i)

/- English proof (translation)
Take `⟨m, f, g, hf, rfl⟩` from `ha`. Use `⟨m, fun k x' => f k (S.p x'), g, fun k => hT _ (hf k), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x'`. Simplify using `[Finset.sum_apply]`.
-/
theorem inR'_of_inR (hT : ∀ f ∈ N.T i, (fun x' => f (S.p x')) ∈ S.T') {a : N.X i → MatN N i}
    (ha : InR N i r a) : InR' N r S (fun x' => a (S.p x')) := by
  obtain ⟨m, f, g, hf, rfl⟩ := ha
  refine ⟨m, fun k x' => f k (S.p x'), g, fun k => hT _ (hf k), ?_⟩
  funext x'
  simp [Finset.sum_apply]

/- English proof (translation)
Take `⟨⟨hB, -⟩, -, -, -, -, -, ⟨hX0, -⟩, ⟨hTT, hrr, -⟩, -⟩` from `hG`. Establish `hB'` using `inR'_of_inR N r S hTT hB`. Establish `hX0'` using `inR'_of_inR N r S hTT hX0`. Establish `key : ∀ L : List ℕ, (∀ c ∈ L, c ∈ Finset.Icc 1 R.t) → InR' N r S (fun x' => (L.map fun c => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x')).prod)`. Introduce `L`.

Proceed by induction on `L with`. Consider the case `nil => intro _`. Conclude with `inSpan_one N S.T' (fun x' => rO N i r (S.p x'))`. Consider the case `cons c L ih`. Introduce `hL`.

Establish `hc : S.rr c ∈ S.T'` using `hrr c (hL c (by simp))`. Establish `h1 : InR' N r S (fun x' => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x'))`. Use `inSpan_add N S.T' (fun x' => rO N i r (S.p x')) hX0' (inSpan_fmul N S.T' (fun x' => rO N i r (S.p x')) (-S.rr c) (S.T'.neg_mem hc) hB')` as an intermediate fact. Establish `e1 : (fun x' => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x')) = (fun x' => S.X0 (S.p x')) + fun x' => (-S.rr c) x' • S.eB (S.p x')`. Use function extensionality and compare the values at `x'`.

Simplify using `[sub_eq_add_neg, neg_smul]`. Rewrite using `[e1]`. Conclude with `this`. Establish `h2` using `inSpan_mul N S.T' (fun x' => rO N i r (S.p x')) h1 (ih fun c' hc' => hL c' (by simp [hc']))`. Establish `e2 : (fun x' => ((c :: L).map fun c => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x')).prod) = (fun x' => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x')) * fun x' => (L.map fun c => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x')).prod`.

Use function extensionality and compare the values at `x'`. Simplify using the standard rewrite rules. Rewrite using `[e2]`. Conclude with `h2`. Unfold `Eel`.

Apply `key` to reduce the goal to its premises. Introduce `c hc`. Rewrite `hc` using `[List.mem_range'_1]`. Rewrite using `[Finset.mem_Icc]`. Use `R.rank_add_five_le` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem eel_inR' (hG : GoodCongruenceObjects N r ρ π S) : InR' N r S (Eel N S) := by
  obtain ⟨⟨hB, -⟩, -, -, -, -, -, ⟨hX0, -⟩, ⟨hTT, hrr, -⟩, -⟩ := hG
  have hB' := inR'_of_inR N r S hTT hB
  have hX0' := inR'_of_inR N r S hTT hX0
  have key : ∀ L : List ℕ, (∀ c ∈ L, c ∈ Finset.Icc 1 R.t) →
      InR' N r S (fun x' => (L.map fun c => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x')).prod) := by
    intro L
    induction L with
    | nil => intro _; exact inSpan_one N S.T' (fun x' => rO N i r (S.p x'))
    | cons c L ih =>
      intro hL
      have hc : S.rr c ∈ S.T' := hrr c (hL c (by simp))
      have h1 : InR' N r S (fun x' => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x')) := by
        have := inSpan_add N S.T' (fun x' => rO N i r (S.p x')) hX0'
          (inSpan_fmul N S.T' (fun x' => rO N i r (S.p x')) (-S.rr c) (S.T'.neg_mem hc) hB')
        have e1 : (fun x' => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x')) =
            (fun x' => S.X0 (S.p x')) + fun x' => (-S.rr c) x' • S.eB (S.p x') := by
          funext x'
          simp [sub_eq_add_neg, neg_smul]
        rw [e1]
        exact this
      have h2 := inSpan_mul N S.T' (fun x' => rO N i r (S.p x')) h1 (ih fun c' hc' => hL c' (by simp [hc']))
      have e2 : (fun x' => ((c :: L).map fun c => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x')).prod) =
          (fun x' => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x')) *
            fun x' => (L.map fun c => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x')).prod := by
        funext x'
        simp
      rw [e2]
      exact h2
  unfold Eel
  apply key
  intro c hc
  rw [List.mem_range'_1] at hc
  rw [Finset.mem_Icc]
  have := R.rank_add_five_le
  omega

end Main

section Psi

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))
  (π : N.X i) (S : IdempotentChoiceData N i)

/- English proof (translation)
Establish `hIn` using `eel_inR' N r ρ π S hG`. Take `⟨-, -, hR', -, -, -, -, -, -, -, ⟨-, -, hEπ, -⟩, -⟩` from `hG`. Establish `h1` using `hR' (Eel N S) hIn`. Prove the components needed by the constructor for the conclusion. Apply `mat_eq_of_mulVec` to reduce the goal to its premises.

Introduce `v`. Establish `h2` using `congrArg Prod.fst ((h1 (S.e.symm (v, 0))).symm.trans (hEπ _))`. Simplify using `only [LinearEquiv.apply_symm_apply] at h2`. Rewrite using `[h2]`. Simplify using the standard rewrite rules.

Introduce `c`. Establish `h2` using `congrFun (congrArg Prod.snd ((h1 (S.e.symm (0, Pi.single c 1))).symm.trans (hEπ _))) c`. Simplify using `only [LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one] at h2`. Apply `IsFractionRing.injective (N.O i) (KK N i)` to reduce the goal to its premises. Use `split_ifs with hc`.

Rewrite using `[h2, if_pos hc]`. Rewrite using `[h2, if_neg hc, map_zero]`.
-/
theorem psi_E (hG : GoodCongruenceObjects N r ρ π S) :
    S.ψρ (Eel N S) = 0 ∧
    ∀ c : Fin R.t, S.ψχ c (Eel N S) = if (c : ℕ) = 0 then del51 N S S.π' else 0 := by
  have hIn := eel_inR' N r ρ π S hG
  obtain ⟨-, -, hR', -, -, -, -, -, -, -, ⟨-, -, hEπ, -⟩, -⟩ := hG
  have h1 := hR' (Eel N S) hIn
  constructor
  · apply mat_eq_of_mulVec
    intro v
    have h2 := congrArg Prod.fst ((h1 (S.e.symm (v, 0))).symm.trans (hEπ _))
    simp only [LinearEquiv.apply_symm_apply] at h2
    rw [h2]
    simp
  · intro c
    have h2 := congrFun (congrArg Prod.snd ((h1 (S.e.symm (0, Pi.single c 1))).symm.trans (hEπ _))) c
    simp only [LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one] at h2
    apply IsFractionRing.injective (N.O i) (KK N i)
    split_ifs with hc
    · rw [h2, if_pos hc]
    · rw [h2, if_neg hc, map_zero]

/- English proof (translation)
Establish `e : (fun x' => f x' • (1 : MatN N i)) = ∑ k : Fin 1, fun x' => (fun _ : Fin 1 => f) k x' • rO N i r (S.p x') ((fun _ : Fin 1 => (1 : GE N)) k)`. Use function extensionality and compare the values at `x'`. Simplify using the standard rewrite rules. Take `⟨h1, h2⟩` from `psi_sum N r ρ π S hG 1 (fun _ => f) (fun _ => 1) (fun _ => hf)`. Rewrite using `[e]`.

Use `⟨?_, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`. Simplify using the standard rewrite rules. Rewrite using `[h2]`. Simplify using the standard rewrite rules.
-/
theorem psi_scal (hG : GoodCongruenceObjects N r ρ π S) (f : S.X' → N.O i) (hf : f ∈ S.T') :
    S.ψρ (fun x' => f x' • (1 : MatN N i)) = f S.π' • 1 ∧
    ∀ c : Fin R.t, S.ψχ c (fun x' => f x' • (1 : MatN N i)) = f S.π' := by
  have e : (fun x' => f x' • (1 : MatN N i)) =
      ∑ k : Fin 1, fun x' => (fun _ : Fin 1 => f) k x' • rO N i r (S.p x') ((fun _ : Fin 1 => (1 : GE N)) k) := by
    funext x'
    simp
  obtain ⟨h1, h2⟩ := psi_sum N r ρ π S hG 1 (fun _ => f) (fun _ => 1) (fun _ => hf)
  rw [e]
  refine ⟨?_, fun c => ?_⟩
  · rw [h1]; simp
  · rw [h2]; simp

end Psi

section MatQ

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem matQ_mk (A : Matrix (Fin R.r) (Fin R.r) (N.O i)) (u : Fin R.r → KK N i) :
    matQ N A (Submodule.Quotient.mk u) = Submodule.Quotient.mk ((A.map (toK N i)).mulVec u) := rfl

/- English proof (translation)
Proceed by induction on `w using Submodule.Quotient.induction_on with`. Consider the case `H u => rw [matQ_mk, matQ_mk, matQ_mk, Matrix.map_mul, Matrix.mulVec_mulVec]`.
-/
theorem matQ_mul (A B : Matrix (Fin R.r) (Fin R.r) (N.O i)) (w : KOr N i) :
    matQ N (A * B) w = matQ N A (matQ N B w) := by
  induction w using Submodule.Quotient.induction_on with
  | H u => rw [matQ_mk, matQ_mk, matQ_mk, Matrix.map_mul, Matrix.mulVec_mulVec]

/- English proof (translation)
Proceed by induction on `w using Submodule.Quotient.induction_on with`. Consider the case `H u`. Rewrite using `[matQ_mk, matQ_mk, matQ_mk, ← Submodule.Quotient.mk_add, ← Matrix.add_mulVec]`. Use `congr 2`. Use extensionality with `a b`.

Simplify using the standard rewrite rules.
-/
theorem matQ_add (A B : Matrix (Fin R.r) (Fin R.r) (N.O i)) (w : KOr N i) :
    matQ N (A + B) w = matQ N A w + matQ N B w := by
  induction w using Submodule.Quotient.induction_on with
  | H u =>
    rw [matQ_mk, matQ_mk, matQ_mk, ← Submodule.Quotient.mk_add, ← Matrix.add_mulVec]
    congr 2
    ext a b
    simp

/- English proof (translation)
Proceed by induction on `w using Submodule.Quotient.induction_on with`. Consider the case `H u => rw [matQ_mk]`. Simplify using the standard rewrite rules.
-/
theorem matQ_zero (w : KOr N i) : matQ N 0 w = 0 := by
  induction w using Submodule.Quotient.induction_on with
  | H u => rw [matQ_mk]; simp

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [matQ_zero]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, matQ_add, ih]`.
-/
theorem matQ_sum {ι : Type} (s : Finset ι) (A : ι → Matrix (Fin R.r) (Fin R.r) (N.O i)) (w : KOr N i) :
    matQ N (∑ k ∈ s, A k) w = ∑ k ∈ s, matQ N (A k) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [matQ_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, matQ_add, ih]

/- English proof (translation)
Proceed by induction on `w using Submodule.Quotient.induction_on with`. Consider the case `H u`. Rewrite using `[matQ_mk, ← Submodule.Quotient.mk_smul]`. Use `congr 1`. Establish `hm : (c • (1 : Matrix (Fin R.r) (Fin R.r) (N.O i))).map (toK N i) = (toK N i c) • (1 : Matrix (Fin R.r) (Fin R.r) (KK N i))`.

Use extensionality with `a b`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[hm, Matrix.smul_mulVec, Matrix.one_mulVec, algebraMap_smul]`.
-/
theorem matQ_scal (c : N.O i) (w : KOr N i) : matQ N (c • (1 : Matrix (Fin R.r) (Fin R.r) (N.O i))) w = c • w := by
  induction w using Submodule.Quotient.induction_on with
  | H u =>
    rw [matQ_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    have hm : (c • (1 : Matrix (Fin R.r) (Fin R.r) (N.O i))).map (toK N i) =
        (toK N i c) • (1 : Matrix (Fin R.r) (Fin R.r) (KK N i)) := by
      ext a b
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [hm, Matrix.smul_mulVec, Matrix.one_mulVec, algebraMap_smul]

end MatQ

section CoboundaryLemmaNoColumn

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))
  (π : N.X i) (S : IdempotentChoiceData N i)

def zz (m : ℕ) (t : Fin m → S.X' → N.O i) (γ : Fin m → GE N) : S.X' → MatN N i :=
  ∑ k, (fun x' => (t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • (1 : MatN N i)) * yg N r S (γ k)

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, ⟨-, hrr, -⟩, -⟩` from `hG`. Establish `ht` using `R.rank_add_five_le`. Establish `h1 : S.rr 1 ∈ S.T'` using `hrr 1 (by rw [Finset.mem_Icc]; omega)`. Establish `e : del51 N S = ∏ c ∈ Finset.Ioc 1 R.t, (S.rr 1 - S.rr c)`. Use function extensionality and compare the values at `x'`.

Simplify using `[del51, Finset.prod_apply]`. Rewrite using `[e]`. Use `Subalgebra.prod_mem _ fun c hc => S.T'.sub_mem h1 (hrr c ?_)` and prove the remaining obligations. Rewrite `hc` using `[Finset.mem_Ioc]`. Rewrite using `[Finset.mem_Icc]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem congruence_discriminant_mem (hG : GoodCongruenceObjects N r ρ π S) : del51 N S ∈ S.T' := by
  obtain ⟨-, -, -, -, -, -, -, ⟨-, hrr, -⟩, -⟩ := hG
  have ht := R.rank_add_five_le
  have h1 : S.rr 1 ∈ S.T' := hrr 1 (by rw [Finset.mem_Icc]; omega)
  have e : del51 N S = ∏ c ∈ Finset.Ioc 1 R.t, (S.rr 1 - S.rr c) := by
    funext x'
    simp [del51, Finset.prod_apply]
  rw [e]
  refine Subalgebra.prod_mem _ fun c hc => S.T'.sub_mem h1 (hrr c ?_)
  rw [Finset.mem_Ioc] at hc
  rw [Finset.mem_Icc]
  omega

/- English proof (translation)
Use `⟨1, fun _ => 1, fun _ => γ, fun _ => inSpan_one N S.T' (fun x' => rO N i r (S.p x')), ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem yg_inY (γ : GE N) : InY N r S (yg N r S γ) := by
  refine ⟨1, fun _ => 1, fun _ => γ, fun _ => inSpan_one N S.T' (fun x' => rO N i r (S.p x')), ?_⟩
  simp

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, -, -, ⟨-, hEE, -, -⟩, -⟩` from `hG`. Prove the components needed by the constructor for the conclusion. Use `⟨m, fun k x' => (t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • (1 : MatN N i), γ, fun k => inSpan_scal N S.T' _ _ (S.T'.mul_mem (ht k) (S.T'.algebraMap_mem _)), rfl⟩` and prove the remaining obligations. Establish `hz : ∀ x', zz N r S m t γ x' = (del51 N S x' - ∑ k, t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • Eel N S x'`. Introduce `x'`.

Establish `hEx : Eel N S x' = ∑ k, t k x' • rO N i r (S.p x') (γ k)`. Rewrite using `[hE, Finset.sum_apply]`. Establish `step : ∀ k, ((fun x' => (t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • (1 : MatN N i)) * yg N r S (γ k)) x' = t k x' • (rO N i r (S.p x') (γ k) * Eel N S x') - (t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • Eel N S x'`. Introduce `k`. Simplify using `only [Pi.mul_apply, yg]`.

Rewrite using `[smul_one_mul, smul_sub, smul_smul, Units.mul_inv_cancel_right]`. Unfold `zz`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [step]`. Rewrite using `[Finset.sum_sub_distrib, ← Finset.sum_smul]`.

Establish `hA : ∑ k, t k x' • (rO N i r (S.p x') (γ k) * Eel N S x') = Eel N S x' * Eel N S x'` using `by conv_rhs => rw [hEx]`. Rewrite using `[Finset.sum_mul]`. Simplify using `only [smul_mul_assoc]`. Rewrite using `[← hEx]`. Rewrite using `[hA, hEE, sub_smul]`.

Use function extensionality and compare the values at `x'`. Simplify using `only [Pi.mul_apply]`. Rewrite using `[hz, smul_one_mul, mul_smul_comm, hEE, smul_comm]`.
-/
theorem zz_facts (hG : GoodCongruenceObjects N r ρ π S) (m : ℕ) (t : Fin m → S.X' → N.O i) (γ : Fin m → GE N)
    (ht : ∀ k, t k ∈ S.T') (hE : Eel N S = ∑ k, fun x' => t k x' • rO N i r (S.p x') (γ k)) :
    InY N r S (zz N r S m t γ) ∧
    Eel N S * zz N r S m t γ = (fun x' => del51 N S x' • (1 : MatN N i)) * zz N r S m t γ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨-, hEE, -, -⟩, -⟩ := hG
  constructor
  · refine ⟨m, fun k x' => (t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • (1 : MatN N i), γ,
      fun k => inSpan_scal N S.T' _ _ (S.T'.mul_mem (ht k) (S.T'.algebraMap_mem _)), rfl⟩
  · have hz : ∀ x', zz N r S m t γ x' =
        (del51 N S x' - ∑ k, t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • Eel N S x' := by
      intro x'
      have hEx : Eel N S x' = ∑ k, t k x' • rO N i r (S.p x') (γ k) := by
        rw [hE, Finset.sum_apply]
      have step : ∀ k, ((fun x' => (t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • (1 : MatN N i)) *
          yg N r S (γ k)) x' = t k x' • (rO N i r (S.p x') (γ k) * Eel N S x') -
            (t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • Eel N S x' := by
        intro k
        simp only [Pi.mul_apply, yg]
        rw [smul_one_mul, smul_sub, smul_smul, Units.mul_inv_cancel_right]
      unfold zz
      rw [Finset.sum_apply]
      simp only [step]
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
      have hA : ∑ k, t k x' • (rO N i r (S.p x') (γ k) * Eel N S x') = Eel N S x' * Eel N S x' := by
        conv_rhs => rw [hEx]
        rw [Finset.sum_mul]
        simp only [smul_mul_assoc]
        rw [← hEx]
      rw [hA, hEE, sub_smul]
    funext x'
    simp only [Pi.mul_apply]
    rw [hz, smul_one_mul, mul_smul_comm, hEE, smul_comm]

/- English proof (translation)
Establish `hEin` using `eel_inR' N r ρ π S hG`. Take `⟨m, t, γ, ht, hE⟩` from `hEin`. Take `⟨hY, hEz⟩` from `zz_facts N r ρ π S hG m t γ ht hE`. Take `⟨hψρ, hψχ⟩` from `psi_E N r ρ π S hG`. Take `⟨hsρ, hsχ⟩` from `psi_sum N r ρ π S hG m t γ ht`.

Rewrite `hsρ`, `hsχ` using `[← hE]`. Establish `h0 : 0 < R.t` using `by have := R.rank_add_five_le; omega`. Establish `hsumρ : ∑ k, t k S.π' • rhoO N i ρ π (γ k) = 0` using `by rw [← hsρ, hψρ]`. Establish `hsumχ : ∑ k, t k S.π' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i) = del51 N S S.π'`. Use `hsχ ⟨0, h0⟩` as an intermediate fact.

Rewrite `this` using `[hψχ ⟨0, h0⟩]`. Simplify using `using this.symm`. Establish `hφz : φ (zz N r S m t γ) = (-(del51 N S S.π')) • w`. Unfold `zz`. Rewrite using `[map_sum]`.

Establish `hk : ∀ k, φ ((fun x' => (t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • (1 : MatN N i)) * yg N r S (γ k)) = matQ N (((t k S.π' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • (1 : Matrix (Fin R.r) (Fin R.r) (N.O i))) * ((((chiU N i 1 (γ k))⁻¹ : (N.O i)ˣ) : N.O i) • rhoO N i ρ π …`. Introduce `k`. Establish `hmem : (fun x' => t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) ∈ S.T'` using `S.T'.mul_mem (ht k) (S.T'.algebraMap_mem ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i))`. Rewrite using `[h1 _ (inSpan_scal N S.T' _ _ hmem) _ (yg_inY N r S (γ k)), (psi_scal N r ρ π S hG _ hmem).1, h2, matQ_mul]`. Simplify using `only [hk]`.

Rewrite using `[← matQ_sum]`. Establish `hm : ∑ k, ((t k S.π' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • (1 : Matrix (Fin R.r) (Fin R.r) (N.O i))) * ((((chiU N i 1 (γ k))⁻¹ : (N.O i)ˣ) : N.O i) • rhoO N i ρ π (γ k) - 1) = (-(del51 N S S.π')) • (1 : Matrix (Fin R.r) (Fin R.r) (N.O i))`. Establish `e1 : ∀ k, ((t k S.π' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • (1 : Matrix (Fin R.r) (Fin R.r) (N.O i))) * ((((chiU N i 1 (γ k))⁻¹ : (N.O i)ˣ) : N.O i) • rhoO N i ρ π (γ k) - 1) = t k S.π' • rhoO N i ρ π (γ k) - (t k S.π' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • (1 : Matri …`. Introduce `k`. Rewrite using `[smul_one_mul, smul_sub, smul_smul, Units.mul_inv_cancel_right]`.

Simplify using `only [e1]`. Rewrite using `[Finset.sum_sub_distrib, ← Finset.sum_smul, hsumρ, hsumχ, zero_sub, neg_smul]`. Rewrite using `[hm, matQ_scal]`. Establish `hA : φ (Eel N S * zz N r S m t γ) = 0`. Rewrite using `[h1 _ (eel_inR' N r ρ π S hG) _ hY, hψρ, matQ_zero]`.

Establish `hB : φ ((fun x' => del51 N S x' • (1 : MatN N i)) * zz N r S m t γ) = del51 N S S.π' • φ (zz N r S m t γ)`. Rewrite using `[h1 _ (inSpan_scal N S.T' _ _ (congruence_discriminant_mem N r ρ π S hG)) _ hY, (psi_scal N r ρ π S hG _ (congruence_discriminant_mem N r ρ π S hG)).1, matQ_scal]`. Rewrite `hA` using `[hEz, hB, hφz, smul_smul]`. Rewrite using `[pow_two]`. Establish `: (del51 N S S.π' * del51 N S S.π') • w = -((del51 N S S.π' * -del51 N S S.π') • w)`.

Rewrite using `[← neg_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hA, neg_zero]`.
-/
theorem congruence_annihilates_rho_part (hG : GoodCongruenceObjects N r ρ π S) (φ : (S.X' → MatN N i) →ₗ[N.O i] KOr N i) (w : KOr N i)
    (h1 : ∀ a, InR' N r S a → ∀ y, InY N r S y → φ (a * y) = matQ N (S.ψρ a) (φ y))
    (h2 : ∀ γ : GE N, φ (yg N r S γ) =
      matQ N ((((chiU N i 1 γ)⁻¹ : (N.O i)ˣ) : N.O i) • rhoO N i ρ π γ - 1) w) :
    del51 N S S.π' ^ 2 • w = 0 := by
  have hEin := eel_inR' N r ρ π S hG
  obtain ⟨m, t, γ, ht, hE⟩ := hEin
  obtain ⟨hY, hEz⟩ := zz_facts N r ρ π S hG m t γ ht hE
  obtain ⟨hψρ, hψχ⟩ := psi_E N r ρ π S hG
  obtain ⟨hsρ, hsχ⟩ := psi_sum N r ρ π S hG m t γ ht
  rw [← hE] at hsρ hsχ
  have h0 : 0 < R.t := by have := R.rank_add_five_le; omega
  have hsumρ : ∑ k, t k S.π' • rhoO N i ρ π (γ k) = 0 := by rw [← hsρ, hψρ]
  have hsumχ : ∑ k, t k S.π' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i) = del51 N S S.π' := by
    have := hsχ ⟨0, h0⟩
    rw [hψχ ⟨0, h0⟩] at this
    simpa using this.symm
  have hφz : φ (zz N r S m t γ) = (-(del51 N S S.π')) • w := by
    unfold zz
    rw [map_sum]
    have hk : ∀ k, φ ((fun x' => (t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • (1 : MatN N i)) *
        yg N r S (γ k)) = matQ N (((t k S.π' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) •
          (1 : Matrix (Fin R.r) (Fin R.r) (N.O i))) *
          ((((chiU N i 1 (γ k))⁻¹ : (N.O i)ˣ) : N.O i) • rhoO N i ρ π (γ k) - 1)) w := by
      intro k
      have hmem : (fun x' => t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) ∈ S.T' :=
        S.T'.mul_mem (ht k) (S.T'.algebraMap_mem ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i))
      rw [h1 _ (inSpan_scal N S.T' _ _ hmem) _ (yg_inY N r S (γ k)),
        (psi_scal N r ρ π S hG _ hmem).1, h2, matQ_mul]
    simp only [hk]
    rw [← matQ_sum]
    have hm : ∑ k, ((t k S.π' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) •
          (1 : Matrix (Fin R.r) (Fin R.r) (N.O i))) *
          ((((chiU N i 1 (γ k))⁻¹ : (N.O i)ˣ) : N.O i) • rhoO N i ρ π (γ k) - 1) =
        (-(del51 N S S.π')) • (1 : Matrix (Fin R.r) (Fin R.r) (N.O i)) := by
      have e1 : ∀ k, ((t k S.π' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) •
          (1 : Matrix (Fin R.r) (Fin R.r) (N.O i))) *
          ((((chiU N i 1 (γ k))⁻¹ : (N.O i)ˣ) : N.O i) • rhoO N i ρ π (γ k) - 1) =
          t k S.π' • rhoO N i ρ π (γ k) -
            (t k S.π' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • (1 : Matrix (Fin R.r) (Fin R.r) (N.O i)) := by
        intro k
        rw [smul_one_mul, smul_sub, smul_smul, Units.mul_inv_cancel_right]
      simp only [e1]
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsumρ, hsumχ, zero_sub, neg_smul]
    rw [hm, matQ_scal]
  have hA : φ (Eel N S * zz N r S m t γ) = 0 := by
    rw [h1 _ (eel_inR' N r ρ π S hG) _ hY, hψρ, matQ_zero]
  have hB : φ ((fun x' => del51 N S x' • (1 : MatN N i)) * zz N r S m t γ) =
      del51 N S S.π' • φ (zz N r S m t γ) := by
    rw [h1 _ (inSpan_scal N S.T' _ _ (congruence_discriminant_mem N r ρ π S hG)) _ hY,
      (psi_scal N r ρ π S hG _ (congruence_discriminant_mem N r ρ π S hG)).1, matQ_scal]
  rw [hEz, hB, hφz, smul_smul] at hA
  rw [pow_two]
  have : (del51 N S S.π' * del51 N S S.π') • w = -((del51 N S S.π' * -del51 N S S.π') • w) := by
    rw [← neg_smul]; congr 1; ring
  rw [this, hA, neg_zero]

/- English proof (translation)
Establish `hEin` using `eel_inR' N r ρ π S hG`. Take `⟨m, t, γ, ht, hE⟩` from `hEin`. Take `⟨hY, hEz⟩` from `zz_facts N r ρ π S hG m t γ ht hE`. Take `⟨-, hψχ⟩` from `psi_E N r ρ π S hG`. Take `⟨-, hsχ⟩` from `psi_sum N r ρ π S hG m t γ ht`.

Rewrite `hsχ` using `[← hE]`. Establish `h0 : 0 < R.t` using `by have := R.rank_add_five_le; omega`. Establish `hsumc : ∑ k, t k S.π' * ((chiU N i ((c : ℕ) + 1) (γ k) : (N.O i)ˣ) : N.O i) = 0`. Rewrite using `[← hsχ c, hψχ c, if_neg hc]`. Establish `hsum1 : ∑ k, t k S.π' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i) = del51 N S S.π'`.

Use `hsχ ⟨0, h0⟩` as an intermediate fact. Rewrite `this` using `[hψχ ⟨0, h0⟩]`. Simplify using `using this.symm`. Establish `hφz : φ (zz N r S m t γ) = (-(del51 N S S.π')) • w`. Unfold `zz`.

Rewrite using `[map_sum]`. Establish `hk : ∀ k, φ ((fun x' => (t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • (1 : MatN N i)) * yg N r S (γ k)) = (t k S.π' * ((chiU N i ((c : ℕ) + 1) (γ k) : (N.O i)ˣ) : N.O i) - t k S.π' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • w`. Introduce `k`. Establish `hmem : (fun x' => t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) ∈ S.T'` using `S.T'.mul_mem (ht k) (S.T'.algebraMap_mem ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i))`. Rewrite using `[h1 _ (inSpan_scal N S.T' _ _ hmem) _ (yg_inY N r S (γ k)), (psi_scal N r ρ π S hG _ hmem).2 c, h2, smul_smul]`.

Use `congr 1`. Establish `hu : ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i) * (((chiU N i 1 (γ k))⁻¹ : (N.O i)ˣ) : N.O i) = 1` using `Units.mul_inv _`. Simplify using `only [Units.val_mul]`. Use `show t k S.π' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i) * (((chiU N i ((c : ℕ) + 1) (γ k) : (N.O i)ˣ) : N.O i) * (((chiU N i 1 (γ k))⁻¹ : (N.O i)ˣ) : N.O i) - 1) = _`. Take the linear combination `(t k S.π' * ((chiU N i ((c : ℕ) + 1) (γ k) : (N.O i)ˣ) : N.O i)) * hu`.

Simplify using `only [hk]`. Rewrite using `[← Finset.sum_smul, Finset.sum_sub_distrib, hsumc, hsum1, zero_sub]`. Establish `hA : φ (Eel N S * zz N r S m t γ) = 0`. Rewrite using `[h1 _ (eel_inR' N r ρ π S hG) _ hY, hψχ c, if_neg hc, zero_smul]`. Establish `hB : φ ((fun x' => del51 N S x' • (1 : MatN N i)) * zz N r S m t γ) = del51 N S S.π' • φ (zz N r S m t γ)`.

Rewrite using `[h1 _ (inSpan_scal N S.T' _ _ (congruence_discriminant_mem N r ρ π S hG)) _ hY, (psi_scal N r ρ π S hG _ (congruence_discriminant_mem N r ρ π S hG)).2 c]`. Rewrite `hA` using `[hEz, hB, hφz, smul_smul]`. Rewrite using `[pow_two]`. Establish `: (del51 N S S.π' * del51 N S S.π') • w = -((del51 N S S.π' * -del51 N S S.π') • w)`. Rewrite using `[← neg_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hA, neg_zero]`.
-/
theorem congruence_annihilates_character_part (hG : GoodCongruenceObjects N r ρ π S) (c : Fin R.t) (hc : (c : ℕ) ≠ 0)
    (φ : (S.X' → MatN N i) →ₗ[N.O i] KmodO (N.O i)) (w : KmodO (N.O i))
    (h1 : ∀ a, InR' N r S a → ∀ y, InY N r S y → φ (a * y) = S.ψχ c a • φ y)
    (h2 : ∀ γ : GE N, φ (yg N r S γ) =
      (((chiU N i ((c : ℕ) + 1) γ * (chiU N i 1 γ)⁻¹ : (N.O i)ˣ) : N.O i) - 1) • w) :
    del51 N S S.π' ^ 2 • w = 0 := by
  have hEin := eel_inR' N r ρ π S hG
  obtain ⟨m, t, γ, ht, hE⟩ := hEin
  obtain ⟨hY, hEz⟩ := zz_facts N r ρ π S hG m t γ ht hE
  obtain ⟨-, hψχ⟩ := psi_E N r ρ π S hG
  obtain ⟨-, hsχ⟩ := psi_sum N r ρ π S hG m t γ ht
  rw [← hE] at hsχ
  have h0 : 0 < R.t := by have := R.rank_add_five_le; omega
  have hsumc : ∑ k, t k S.π' * ((chiU N i ((c : ℕ) + 1) (γ k) : (N.O i)ˣ) : N.O i) = 0 := by
    rw [← hsχ c, hψχ c, if_neg hc]
  have hsum1 : ∑ k, t k S.π' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i) = del51 N S S.π' := by
    have := hsχ ⟨0, h0⟩
    rw [hψχ ⟨0, h0⟩] at this
    simpa using this.symm
  have hφz : φ (zz N r S m t γ) = (-(del51 N S S.π')) • w := by
    unfold zz
    rw [map_sum]
    have hk : ∀ k, φ ((fun x' => (t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • (1 : MatN N i)) *
        yg N r S (γ k)) = (t k S.π' * ((chiU N i ((c : ℕ) + 1) (γ k) : (N.O i)ˣ) : N.O i) -
          t k S.π' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) • w := by
      intro k
      have hmem : (fun x' => t k x' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i)) ∈ S.T' :=
        S.T'.mul_mem (ht k) (S.T'.algebraMap_mem ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i))
      rw [h1 _ (inSpan_scal N S.T' _ _ hmem) _ (yg_inY N r S (γ k)),
        (psi_scal N r ρ π S hG _ hmem).2 c, h2, smul_smul]
      congr 1
      have hu : ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i) * (((chiU N i 1 (γ k))⁻¹ : (N.O i)ˣ) : N.O i) = 1 :=
        Units.mul_inv _
      simp only [Units.val_mul]
      show t k S.π' * ((chiU N i 1 (γ k) : (N.O i)ˣ) : N.O i) *
          (((chiU N i ((c : ℕ) + 1) (γ k) : (N.O i)ˣ) : N.O i) *
            (((chiU N i 1 (γ k))⁻¹ : (N.O i)ˣ) : N.O i) - 1) = _
      linear_combination (t k S.π' * ((chiU N i ((c : ℕ) + 1) (γ k) : (N.O i)ˣ) : N.O i)) * hu
    simp only [hk]
    rw [← Finset.sum_smul, Finset.sum_sub_distrib, hsumc, hsum1, zero_sub]
  have hA : φ (Eel N S * zz N r S m t γ) = 0 := by
    rw [h1 _ (eel_inR' N r ρ π S hG) _ hY, hψχ c, if_neg hc, zero_smul]
  have hB : φ ((fun x' => del51 N S x' • (1 : MatN N i)) * zz N r S m t γ) =
      del51 N S S.π' • φ (zz N r S m t γ) := by
    rw [h1 _ (inSpan_scal N S.T' _ _ (congruence_discriminant_mem N r ρ π S hG)) _ hY,
      (psi_scal N r ρ π S hG _ (congruence_discriminant_mem N r ρ π S hG)).2 c]
  rw [hEz, hB, hφz, smul_smul] at hA
  rw [pow_two]
  have : (del51 N S S.π' * del51 N S S.π') • w = -((del51 N S S.π' * -del51 N S S.π') • w) := by
    rw [← neg_smul]; congr 1; ring
  rw [this, hA, neg_zero]

end CoboundaryLemmaNoColumn

section Packet

open Formalism.MainNotions

variable (D : D7)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun φ w h1 h2 => congruence_annihilates_rho_part D.nd r ρ π S hG φ w h1 h2, fun c hc φ w h1 h2 => congruence_annihilates_character_part D.nd r ρ π S hG c hc φ w h1 h2⟩`.
-/
theorem congruence_annihilation_lemma (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (S : IdempotentChoiceData D.nd i)
    (hG : GoodCongruenceObjects D.nd r ρ π S) : PairedCharacterCondition.CoboundaryLemmaNoColumn (D := D) i r ρ π S :=
  ⟨fun φ w h1 h2 => congruence_annihilates_rho_part D.nd r ρ π S hG φ w h1 h2,
    fun c hc φ w h1 h2 => congruence_annihilates_character_part D.nd r ρ π S hG c hc φ w h1 h2⟩

def SupplierRemainingLemmas : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → HG D.nd D.naut i →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r →
    LargeLevelLemmas.CharpolyCoeffsLemmaFamily i r ∧
    ∀ π ∈ D.nd.Z i, TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → LargeLevelLemmas.SpanQuotientLemma i r ρ π ∧ LargeLevelLemmas.HomRelationsLemmaAllChoices i r ρ π

/- English proof (translation)
Introduce `i k hl hG r ρ hr`. Take `⟨h51, hrest⟩` from `h i k hl hG r ρ hr`. Use `⟨h51, fun π hπ hd => ?_⟩` and prove the remaining obligations. Take `⟨h52, h53⟩` from `hrest π hπ hd`. Conclude with `⟨hO i k hl hG r ρ hr π hπ hd, fun S hS _ => ⟨h52 hπ S hS, h53 hπ S hS, congruence_annihilation_lemma D i r ρ π S hS⟩⟩`.
-/
theorem supplier_of_choice_and_lemmas (hO : TypePrimeCongruences.TypePrimeWildIdempotentChoice D) (h : SupplierRemainingLemmas D) : TypePrimeCongruences.TypePrimeChoiceConclusions D := by
  intro i k hl hG r ρ hr
  obtain ⟨h51, hrest⟩ := h i k hl hG r ρ hr
  refine ⟨h51, fun π hπ hd => ?_⟩
  obtain ⟨h52, h53⟩ := hrest π hπ hd
  exact ⟨hO i k hl hG r ρ hr π hπ hd, fun S hS _ => ⟨h52 hπ S hS, h53 hπ S hS, congruence_annihilation_lemma D i r ρ π S hS⟩⟩

end Packet

end Formalism.MainNotions.TypePrimeCongruences.CongruenceModules

end
