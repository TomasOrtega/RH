import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.RgEisSo.JIwaAd

section Dg

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Introduce `r hr c hc`. Establish `hne : r ≠ c` using `fun h => hr (h ▸ hc)`. Conclude with `⟨Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hne⟩`.
-/
theorem dg_mem_stab (s : Set (ι ⊕ ι)) (x : Rˣ) : dg ι x ∈ stab R s := by
  intro r hr c hc
  have hne : r ≠ c := fun h => hr (h ▸ hc)
  exact ⟨Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hne⟩

/- English proof (translation)
Use `haveI : Unique ι := ⟨⟨i⟩, hi⟩`. Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply]`. Use `show (Matrix.diagonal _).det = _`. Rewrite using `[Matrix.det_diagonal, Fintype.prod_sum_type]`.

Simplify using the standard rewrite rules.
-/
theorem det_dg {i : ι} (hi : ∀ y, y = i) (x : Rˣ) : Matrix.GeneralLinearGroup.det (dg ι x) = x := by
  haveI : Unique ι := ⟨⟨i⟩, hi⟩
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal _).det = _
  rw [Matrix.det_diagonal, Fintype.prod_sum_type]
  simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `show (Matrix.diagonal _).map f = Matrix.diagonal _`. Rewrite using `[Matrix.diagonal_map (map_zero f)]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `cases a <;> simp`.
-/
theorem map_dg {S : Type} [CommRing S] (f : R →+* S) (x : Rˣ) :
    Matrix.GeneralLinearGroup.map f (dg ι x) = dg ι (Units.map f.toMonoidHom x) := by
  apply Units.ext
  show (Matrix.diagonal _).map f = Matrix.diagonal _
  rw [Matrix.diagonal_map (map_zero f)]
  congr 1
  funext a
  cases a <;> simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `show Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `cases a <;> simp`.
-/
theorem dg_mul (x y : Rˣ) : dg ι (x * y) = dg ι x * dg ι y := by
  apply Units.ext
  show Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  cases a <;> simp

end Dg

section Ad

variable {E R : Type} [Field E] [CommRing R] (A : Ad E R)

/- English proof (translation)
Use `⟨fun r c => ⟨?_, ?_⟩, fun w => ?_⟩` and prove the remaining obligations. Use `show Matrix.diagonal _ r c ∈ A.O`. Distinguish the cases in `h : r = c`. Substitute `h` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq]`.

Apply the tactic sequence `cases r <;> simp [h1, A.O.one_mem]`. Rewrite using `[Matrix.diagonal_apply_ne _ h]`. Conclude with `A.O.zero_mem`. Use `show Matrix.diagonal _ r c ∈ A.O`. Distinguish the cases in `h : r = c`.

Substitute `h` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq]`. Apply the tactic sequence `cases r <;> simp [h2, A.O.one_mem]`. Rewrite using `[Matrix.diagonal_apply_ne _ h]`. Conclude with `A.O.zero_mem`.

Use `show (Matrix.diagonal _).map (A.φ w) ∈ Matrix.unitaryGroup _ ℂ`. Rewrite using `[Matrix.diagonal_map (map_zero _), Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Consider the cases of `a with`.

Consider the case `inl a => simp`. Consider the case `inr a`. Simplify using `only [Function.comp, Sum.elim_inr, Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h3 w]`. Simplify using the standard rewrite rules.
-/
theorem dg_mem_kGL {ι : Type} [Fintype ι] [DecidableEq ι] (x : Rˣ) (h1 : (x : R) ∈ A.O)
    (h2 : ((x⁻¹ : Rˣ) : R) ∈ A.O) (h3 : ∀ w, ‖A.φ w x‖ = 1) : dg ι x ∈ A.kGL (ι ⊕ ι) := by
  refine ⟨fun r c => ⟨?_, ?_⟩, fun w => ?_⟩
  · show Matrix.diagonal _ r c ∈ A.O
    by_cases h : r = c
    · subst h
      rw [Matrix.diagonal_apply_eq]
      cases r <;> simp [h1, A.O.one_mem]
    · rw [Matrix.diagonal_apply_ne _ h]
      exact A.O.zero_mem
  · show Matrix.diagonal _ r c ∈ A.O
    by_cases h : r = c
    · subst h
      rw [Matrix.diagonal_apply_eq]
      cases r <;> simp [h2, A.O.one_mem]
    · rw [Matrix.diagonal_apply_ne _ h]
      exact A.O.zero_mem
  · show (Matrix.diagonal _).map (A.φ w) ∈ Matrix.unitaryGroup _ ℂ
    rw [Matrix.diagonal_map (map_zero _), Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    cases a with
    | inl a => simp
    | inr a =>
      simp only [Function.comp, Sum.elim_inr, Pi.star_apply, RCLike.star_def, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, h3 w]
      simp

variable {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Conclude with `A.O.sum_mem fun s _ => A.O.mul_mem (intCast_mem _ _) (A.O.prod_mem fun m _ => h _ _)`.
-/
theorem det_mem_O {M : Matrix n n R} (h : ∀ r c, M r c ∈ A.O) : M.det ∈ A.O := by
  rw [Matrix.det_apply']
  exact A.O.sum_mem fun s _ => A.O.mul_mem (intCast_mem _ _) (A.O.prod_mem fun m _ => h _ _)

/- English proof (translation)
Use `⟨?_, ?_, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `det_mem_O A fun r c => (hk.1 r c).1`. Rewrite using `[← map_inv, Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `det_mem_O A fun r c => (hk.1 r c).2`.

Establish `h` using `Matrix.det_of_mem_unitary (hk.2 w)`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]`. Establish `h' : star (RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det * (RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det = 1` using `Unitary.star_mul_self_of_mem h`. Establish `h2 : ‖(RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det‖ ^ 2 = 1`. Use `congrArg norm h'` as an intermediate fact.

Simplify `this` using `[sq]`. Use polynomial arithmetic with `[norm_nonneg (RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det, sq_nonneg (‖(RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det‖ - 1)]`.
-/
theorem det_kGL {k : GL n R} (hk : k ∈ A.kGL n) :
    ((Matrix.GeneralLinearGroup.det k : Rˣ) : R) ∈ A.O ∧
      (((Matrix.GeneralLinearGroup.det k)⁻¹ : Rˣ) : R) ∈ A.O ∧
      ∀ w, ‖A.φ w (Matrix.GeneralLinearGroup.det k : Rˣ)‖ = 1 := by
  refine ⟨?_, ?_, fun w => ?_⟩
  · rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact det_mem_O A fun r c => (hk.1 r c).1
  · rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_mem_O A fun r c => (hk.1 r c).2
  · have h := Matrix.det_of_mem_unitary (hk.2 w)
    rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    have h' : star (RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det * (RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det = 1 :=
      Unitary.star_mul_self_of_mem h
    have h2 : ‖(RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det‖ ^ 2 = 1 := by
      have := congrArg norm h'
      simpa [sq] using this
    nlinarith [norm_nonneg (RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det, sq_nonneg (‖(RingHom.mapMatrix (A.φ w) (k : Matrix n n R)).det‖ - 1)]

end Ad

section Main

open GroundTheory.Global

variable {F E R : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [CommRing R] [TopologicalSpace R]

/- English proof (translation)
Use `⟨fun a b => ⟨(hB.int _).2 (hk.1 a b).1, ?_⟩, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `(hB.int _).2 (hk.1 a b).2`. Take `⟨v, hv⟩` from `hB.inf w`. Establish `e : ((Matrix.GeneralLinearGroup.map ν k : GL n R) : Matrix n n R).map (A.φ w) = (k : Matrix n n 𝔸[F]).map ((adStd F).φ v)`.

Use extensionality with `a b`. Simplify using `[hv]`. Rewrite using `[e]`. Conclude with `hk.2 v`.
-/
theorem map_mem_kGL {A : Ad E R} {ε : ℤˣ} {ν : 𝔸[F] →+* R} {r : R → 𝔸[F]} {δ : Eˣ} {α : IdeleGroup F}
    {ω : HeckeCharacter F} (hB : Base A ε ν r δ α ω) {n : Type} [Fintype n] [DecidableEq n]
    {k : GL n 𝔸[F]} (hk : k ∈ (adStd F).kGL n) : Matrix.GeneralLinearGroup.map ν k ∈ A.kGL n := by
  refine ⟨fun a b => ⟨(hB.int _).2 (hk.1 a b).1, ?_⟩, fun w => ?_⟩
  · rw [← map_inv]
    exact (hB.int _).2 (hk.1 a b).2
  · obtain ⟨v, hv⟩ := hB.inf w
    have e : ((Matrix.GeneralLinearGroup.map ν k : GL n R) : Matrix n n R).map (A.φ w) =
        (k : Matrix n n 𝔸[F]).map ((adStd F).φ v) := by
      ext a b
      simp [hv]
    rw [e]
    exact hk.2 v

/- English proof (translation)
Introduce `hS F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hG hB hi hJ x`. Take `⟨b, hb, κ, hκ, hbk⟩` from `(hS F).iwa (ι ⊕ ι) {Sum.inl i} ((dg ι α)⁻¹ * x.1.2 * dg ι α)`. Take `⟨c1, c2, c3⟩` from `det_kGL (adStd F) hκ`. Use `set c := Matrix.GeneralLinearGroup.det κ with hc`. Establish `ht : dg ι c ∈ (adStd F).kGL (ι ⊕ ι)` using `dg_mem_kGL _ c c1 c2 c3`.

Use `set κ' : GL (ι ⊕ ι) 𝔸[F] := (dg ι c)⁻¹ * κ with hκ'`. Establish `hκ'K : κ' ∈ (adStd F).kGL (ι ⊕ ι)` using `mul_mem (inv_mem ht) hκ`. Establish `hdet : Matrix.GeneralLinearGroup.det κ' = 1`. Rewrite using `[hκ', map_mul, map_inv, det_dg hi, ← hc, inv_mul_cancel]`. Use `set d : GL (ι ⊕ ι) 𝔸[F] := dg ι α with hd`.

Establish `hdet2 : Matrix.GeneralLinearGroup.det (d * κ' * d⁻¹) = 1`. Simplify using `[map_mul, hdet, mul_comm]`. Establish `hkc : ((1 : Rˣ), d * κ' * d⁻¹) ∈ cover A ν ι`. Simplify using `[cover, MonoidHom.mem_ker, hdet2]`. Set `k : cover A ν ι` to `⟨_, hkc⟩`.

Establish `hjk : (j k).1 ∈ A.kGL (ι ⊕ ι)`. Take `⟨u, hu, u1, u2, u3⟩` from `hB.δα`. Establish `hδ : Units.map A.i.toMonoidHom δ = Units.map ν.toMonoidHom α * u` using `Units.ext hu`. Establish `e : (j k).1 = (dg ι (Units.map A.i.toMonoidHom δ))⁻¹ * Matrix.GeneralLinearGroup.map ν k.1.2 * dg ι (Units.map A.i.toMonoidHom δ)`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[hJ k]`. Use `show ((1 : Rˣ) : R) • _ = _`. Rewrite using `[Units.val_one, one_smul]`. Establish `e2 : (j k).1 = (dg ι u)⁻¹ * Matrix.GeneralLinearGroup.map ν κ' * dg ι u`. Establish `hD : dg ι (Units.map ν.toMonoidHom α) = Matrix.GeneralLinearGroup.map ν d` using `(map_dg ν α).symm`.

Establish `hk2 : Matrix.GeneralLinearGroup.map ν k.1.2 = Matrix.GeneralLinearGroup.map ν d * Matrix.GeneralLinearGroup.map ν κ' * (Matrix.GeneralLinearGroup.map ν d)⁻¹` using `by show Matrix.GeneralLinearGroup.map ν (d * κ' * d⁻¹) = _`. Rewrite using `[map_mul, map_mul, map_inv]`. Rewrite using `[e, hδ, dg_mul, hD, hk2]`. Generalize the expression as in `Matrix.GeneralLinearGroup.map ν d = P`. Generalize the expression as in `Matrix.GeneralLinearGroup.map ν κ' = Q`.

Generalize the expression as in `dg ι u = T`. Use `group`. Rewrite using `[e2]`. Establish `hU : dg ι u ∈ A.kGL (ι ⊕ ι)` using `dg_mem_kGL A u u1 u2 u3`. Conclude with `mul_mem (mul_mem (inv_mem hU) (map_mem_kGL hB hκ'K)) hU`.

Establish `hkK : k ∈ cK α j`. Use `⟨hjk, ?_⟩` and prove the remaining obligations. Conclude with `⟨κ', hκ'K, rfl⟩`. Use `⟨x * k⁻¹, ?_, k, hkK, by simp⟩` and prove the remaining obligations. Establish `hx : x.1.2 = d * (b * κ) * d⁻¹`.

Rewrite using `[← hbk]`. Use `group`. Establish `hp : prj A ν ι (x * k⁻¹) = d * (b * dg ι c) * d⁻¹`. Rewrite using `[map_mul, map_inv]`. Use `show x.1.2 * (d * κ' * d⁻¹)⁻¹ = _`.

Rewrite using `[hx, hκ']`. Use `group`. Use `show prj A ν ι (x * k⁻¹) ∈ stab 𝔸[F] {Sum.inl i}`. Rewrite using `[hp]`. Establish `hdS : d ∈ stab 𝔸[F] ({Sum.inl i} : Set (ι ⊕ ι))` using `dg_mem_stab _ _`.

Conclude with `mul_mem (mul_mem hdS (mul_mem hb (dg_mem_stab _ _))) (inv_mem hdS)`.
-/
theorem jiwa : StdGood → JIwa := by
  intro hS F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hG hB hi hJ x
  obtain ⟨b, hb, κ, hκ, hbk⟩ := (hS F).iwa (ι ⊕ ι) {Sum.inl i} ((dg ι α)⁻¹ * x.1.2 * dg ι α)
  obtain ⟨c1, c2, c3⟩ := det_kGL (adStd F) hκ
  set c := Matrix.GeneralLinearGroup.det κ with hc
  have ht : dg ι c ∈ (adStd F).kGL (ι ⊕ ι) := dg_mem_kGL _ c c1 c2 c3
  set κ' : GL (ι ⊕ ι) 𝔸[F] := (dg ι c)⁻¹ * κ with hκ'
  have hκ'K : κ' ∈ (adStd F).kGL (ι ⊕ ι) := mul_mem (inv_mem ht) hκ
  have hdet : Matrix.GeneralLinearGroup.det κ' = 1 := by
    rw [hκ', map_mul, map_inv, det_dg hi, ← hc, inv_mul_cancel]
  set d : GL (ι ⊕ ι) 𝔸[F] := dg ι α with hd
  have hdet2 : Matrix.GeneralLinearGroup.det (d * κ' * d⁻¹) = 1 := by
    simp [map_mul, hdet, mul_comm]
  have hkc : ((1 : Rˣ), d * κ' * d⁻¹) ∈ cover A ν ι := by
    simp [cover, MonoidHom.mem_ker, hdet2]
  let k : cover A ν ι := ⟨_, hkc⟩
  have hjk : (j k).1 ∈ A.kGL (ι ⊕ ι) := by
    obtain ⟨u, hu, u1, u2, u3⟩ := hB.δα
    have hδ : Units.map A.i.toMonoidHom δ = Units.map ν.toMonoidHom α * u := Units.ext hu
    have e : (j k).1 = (dg ι (Units.map A.i.toMonoidHom δ))⁻¹ * Matrix.GeneralLinearGroup.map ν k.1.2 *
        dg ι (Units.map A.i.toMonoidHom δ) := by
      apply Units.ext
      rw [hJ k]
      show ((1 : Rˣ) : R) • _ = _
      rw [Units.val_one, one_smul]
    have e2 : (j k).1 = (dg ι u)⁻¹ * Matrix.GeneralLinearGroup.map ν κ' * dg ι u := by
      have hD : dg ι (Units.map ν.toMonoidHom α) = Matrix.GeneralLinearGroup.map ν d := (map_dg ν α).symm
      have hk2 : Matrix.GeneralLinearGroup.map ν k.1.2 = Matrix.GeneralLinearGroup.map ν d *
          Matrix.GeneralLinearGroup.map ν κ' * (Matrix.GeneralLinearGroup.map ν d)⁻¹ := by
        show Matrix.GeneralLinearGroup.map ν (d * κ' * d⁻¹) = _
        rw [map_mul, map_mul, map_inv]
      rw [e, hδ, dg_mul, hD, hk2]
      generalize Matrix.GeneralLinearGroup.map ν d = P
      generalize Matrix.GeneralLinearGroup.map ν κ' = Q
      generalize dg ι u = T
      group
    rw [e2]
    have hU : dg ι u ∈ A.kGL (ι ⊕ ι) := dg_mem_kGL A u u1 u2 u3
    exact mul_mem (mul_mem (inv_mem hU) (map_mem_kGL hB hκ'K)) hU
  have hkK : k ∈ cK α j := by
    refine ⟨hjk, ?_⟩
    exact ⟨κ', hκ'K, rfl⟩
  refine ⟨x * k⁻¹, ?_, k, hkK, by simp⟩
  have hx : x.1.2 = d * (b * κ) * d⁻¹ := by
    rw [← hbk]
    group
  have hp : prj A ν ι (x * k⁻¹) = d * (b * dg ι c) * d⁻¹ := by
    rw [map_mul, map_inv]
    show x.1.2 * (d * κ' * d⁻¹)⁻¹ = _
    rw [hx, hκ']
    group
  show prj A ν ι (x * k⁻¹) ∈ stab 𝔸[F] {Sum.inl i}
  rw [hp]
  have hdS : d ∈ stab 𝔸[F] ({Sum.inl i} : Set (ι ⊕ ι)) := dg_mem_stab _ _
  exact mul_mem (mul_mem hdS (mul_mem hb (dg_mem_stab _ _))) (inv_mem hdS)

end Main

end GlobalTheory.CompanionTheory.RgEisSo.JIwaAd
