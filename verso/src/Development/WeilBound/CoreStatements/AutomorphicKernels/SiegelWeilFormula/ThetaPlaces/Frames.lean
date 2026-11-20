import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.RelReal

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[hcm.2.2.2, hcm.2.2.2, star_star]`.
-/
theorem sig_invol (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [hcm.2.2.2, hcm.2.2.2, star_star]

omit [NumberField F] [NumberField E] in

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hM, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_form {ι κ : Type} [Fintype ι] [Fintype κ] (hσ : ∀ x, σ (σ x) = x) (M : Matrix κ κ E) (b : Matrix κ ι E)
    (s : E) (hM : ∀ k l, σ (M l k) = s * M k l) (i j : ι) :
    σ ((bᵀ * M * b.map σ) j i) = s * (bᵀ * M * b.map σ) i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hM, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Apply the tactic sequence `rcases k with k | k <;> rcases l with l | l <;> simp [GlobalTheory.WeilM.dbl, hJ]`.
-/
theorem dbl_conj {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (hJ : ∀ i j, σ (J j i) = s * J i j)
    (k l : Fin n ⊕ Fin n) : σ (GlobalTheory.WeilM.dbl J l k) = s * GlobalTheory.WeilM.dbl J k l := by
  rcases k with k | k <;> rcases l with l | l <;> simp [GlobalTheory.WeilM.dbl, hJ]

/- English proof (translation)
Establish `hσ` using `sig_invol hcm`. Use `set i0 : Fin d.n := ⟨0, d.ok.hn⟩`. Establish `key` using `conj_form hσ (GlobalTheory.WeilM.dbl d.Y.J) d.b.1 s (dbl_conj d.Y.J s hY) (Sum.inr i0) (Sum.inl i0)`. Rewrite `key` using `[R.hε]`. Simplify using `using key.symm`.
-/
theorem eps_of_form {d : SD σ} (R : RD d) (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (s : E)
    (hY : ∀ i j, σ (d.Y.J j i) = s * d.Y.J i j) : s * ((R.ε : ℤ) : E) = 1 := by
  have hσ := sig_invol hcm
  set i0 : Fin d.n := ⟨0, d.ok.hn⟩
  have key := conj_form hσ (GlobalTheory.WeilM.dbl d.Y.J) d.b.1 s (dbl_conj d.Y.J s hY) (Sum.inr i0) (Sum.inl i0)
  rw [R.hε] at key
  simpa using key.symm

/- English proof (translation)
Establish `h2 : (1 : E) ≠ -1`. Introduce `h`. Establish `: (2 : E) = 0` using `by linear_combination h`. Conclude with `two_ne_zero this`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Break down `R.hζ with ⟨_, hz⟩ | ⟨he, _⟩` into its components or cases. Conclude with `hz`. Rewrite using `[he] at h; exact absurd (by simpa using h) h2`. Introduce `h`.

Break down `R.hζ with ⟨he, _⟩ | ⟨_, hz⟩` into its components or cases. Rewrite using `[he] at h; exact absurd (by simpa using h.symm) h2`. Conclude with `hz`.
-/
theorem zeta_of_eps {d : SD σ} (R : RD d) :
    (((R.ε : ℤ) : E) = -1 → R.ζ = 1) ∧ (((R.ε : ℤ) : E) = 1 → R.ζ = Complex.I) := by
  have h2 : (1 : E) ≠ -1 := by
    intro h
    have : (2 : E) = 0 := by linear_combination h
    exact two_ne_zero this
  constructor
  · intro h
    rcases R.hζ with ⟨_, hz⟩ | ⟨he, _⟩
    · exact hz
    · rw [he] at h; exact absurd (by simpa using h) h2
  · intro h
    rcases R.hζ with ⟨he, _⟩ | ⟨_, hz⟩
    · rw [he] at h; exact absurd (by simpa using h.symm) h2
    · exact hz

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hJ : d.A.J = 0` using `Matrix.ext hcon`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hm` using `d.ok.hm`.

Establish `fin : ∀ (A : Matrix (Fin d.m) (Fin d.r ⊕ Fin d.s) ℂ), d.r + d.s = d.m → Aᵀ * (0 : Matrix (Fin d.m) (Fin d.m) ℂ) * A.map star = Matrix.fromBlocks 1 0 0 (-1) → False`. Introduce `A hrs hA`. Rewrite `hA` using `[Matrix.mul_zero, Matrix.zero_mul]`. Break down `Nat.eq_zero_or_pos d.r with hr | hr` into its components or cases. Establish `hs : 0 < d.s` using `by omega`.

Use `congrFun (congrFun hA (Sum.inr ⟨0, hs⟩)) (Sum.inr ⟨0, hs⟩)` as an intermediate fact. Simplify using `at this`. Use `congrFun (congrFun hA (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)` as an intermediate fact. Simplify using `at this`. Break down `d.ok.sign with ⟨hA, _⟩ | ⟨hA, _⟩` into its components or cases.

Take `⟨hrs, A, hA'⟩` from `hA.sig (InfinitePlace.mk (φ.comp (algebraMap F E)))`. Rewrite `hA'` using `[hJ]`. Conclude with `fin A hrs (by simpa using hA')`. Take `⟨hrs, A, hA'⟩` from `hA.sig (InfinitePlace.mk (φ.comp (algebraMap F E)))`. Rewrite `hA'` using `[hJ]`.

Conclude with `fin A hrs (by simpa using hA')`.
-/
theorem exists_J_ne (d : SD σ) : ∃ i j, d.A.J i j ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hJ : d.A.J = 0 := Matrix.ext hcon
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hm := d.ok.hm
  have fin : ∀ (A : Matrix (Fin d.m) (Fin d.r ⊕ Fin d.s) ℂ),
      d.r + d.s = d.m → Aᵀ * (0 : Matrix (Fin d.m) (Fin d.m) ℂ) * A.map star = Matrix.fromBlocks 1 0 0 (-1) → False := by
    intro A hrs hA
    rw [Matrix.mul_zero, Matrix.zero_mul] at hA
    rcases Nat.eq_zero_or_pos d.r with hr | hr
    · have hs : 0 < d.s := by omega
      have := congrFun (congrFun hA (Sum.inr ⟨0, hs⟩)) (Sum.inr ⟨0, hs⟩)
      simp at this
    · have := congrFun (congrFun hA (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)
      simp at this
  rcases d.ok.sign with ⟨hA, _⟩ | ⟨hA, _⟩
  · obtain ⟨hrs, A, hA'⟩ := hA.sig (InfinitePlace.mk (φ.comp (algebraMap F E)))
    rw [hJ] at hA'
    exact fin A hrs (by simpa using hA')
  · obtain ⟨hrs, A, hA'⟩ := hA.sig (InfinitePlace.mk (φ.comp (algebraMap F E)))
    rw [hJ] at hA'
    exact fin A hrs (by simpa using hA')

/- English proof (translation)
Take `⟨i, j, hij⟩` from `exists_J_ne d`. Establish `h1` using `hA.herm i j`. Establish `h2` using `hA'.skew i j`. Rewrite `h2` using `[h1]`. Establish `: (2 : E) * d.A.J i j = 0` using `by linear_combination h2`.

Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `two_ne_zero h`. Conclude with `hij h`.
-/
theorem not_herm_skew (d : SD σ) (hA : d.A.IsHerm σ d.B d.r d.s) (hA' : d.A.IsSkew σ d.B d.r d.s) : False := by
  obtain ⟨i, j, hij⟩ := exists_J_ne d
  have h1 := hA.herm i j
  have h2 := hA'.skew i j
  rw [h1] at h2
  have : (2 : E) * d.A.J i j = 0 := by linear_combination h2
  rcases mul_eq_zero.1 this with h | h
  · exact two_ne_zero h
  · exact hij h

/- English proof (translation)
Establish `hcm` using `d.ok.good.cm`. Prove the components needed by the constructor for the conclusion. Introduce `hA`. Break down `d.ok.sign with ⟨_, hY⟩ | ⟨hA', _⟩` into its components or cases. Use `(zeta_of_eps R).1 ?_` and prove the remaining obligations.

Use `eps_of_form R hcm (-1) (fun i j => by rw [hY]; ring)` as an intermediate fact. Take the linear combination `-this`. Conclude with `(not_herm_skew d hA hA').elim`. Introduce `hA`. Break down `d.ok.sign with ⟨hA', _⟩ | ⟨_, hY⟩` into its components or cases.

Conclude with `(not_herm_skew d hA' hA).elim`. Use `(zeta_of_eps R).2 ?_` and prove the remaining obligations. Use `eps_of_form R hcm 1 (fun i j => by rw [hY]; ring)` as an intermediate fact. Take the linear combination `this`.
-/
theorem zeta_of_sign' {d : SD σ} (R : RD d) :
    (d.A.IsHerm σ d.B d.r d.s → R.ζ = 1) ∧ (d.A.IsSkew σ d.B d.r d.s → R.ζ = Complex.I) := by
  have hcm := d.ok.good.cm
  constructor
  · intro hA
    rcases d.ok.sign with ⟨_, hY⟩ | ⟨hA', _⟩
    · refine (zeta_of_eps R).1 ?_
      have := eps_of_form R hcm (-1) (fun i j => by rw [hY]; ring)
      linear_combination -this
    · exact (not_herm_skew d hA hA').elim
  · intro hA
    rcases d.ok.sign with ⟨hA', _⟩ | ⟨_, hY⟩
    · exact (not_herm_skew d hA' hA).elim
    · refine (zeta_of_eps R).2 ?_
      have := eps_of_form R hcm 1 (fun i j => by rw [hY]; ring)
      linear_combination this

/- English proof (translation)
Take `⟨i, j, hij⟩` from `exists_J_ne d`. Break down `d.ok.sign with ⟨hA, _⟩ | ⟨hA, _⟩` into its components or cases. Use `left`. Use `⟨?_, (zeta_of_sign' R).1 hA⟩` and prove the remaining obligations. Establish `h` using `herm i j`.

Rewrite `h` using `[map_mul, hA.herm]`. Conclude with `mul_right_cancel₀ hij h`. Use `right`. Use `⟨?_, (zeta_of_sign' R).2 hA⟩` and prove the remaining obligations. Establish `h` using `herm i j`.

Rewrite `h` using `[map_mul, hA.skew]`. Establish `: (σ η + η) * d.A.J i j = 0` using `by linear_combination -h`. Break down `mul_eq_zero.1 this with h' | h'` into its components or cases. Take the linear combination `h'`. Conclude with `(hij h').elim`.
-/
theorem eta_zeta' {d : SD σ} (R : RD d) {η : E} (hη : η ≠ 0) (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    (σ η = η ∧ R.ζ = 1) ∨ (σ η = -η ∧ R.ζ = Complex.I) := by
  obtain ⟨i, j, hij⟩ := exists_J_ne d
  rcases d.ok.sign with ⟨hA, _⟩ | ⟨hA, _⟩
  · left
    refine ⟨?_, (zeta_of_sign' R).1 hA⟩
    have h := herm i j
    rw [map_mul, hA.herm] at h
    exact mul_right_cancel₀ hij h
  · right
    refine ⟨?_, (zeta_of_sign' R).2 hA⟩
    have h := herm i j
    rw [map_mul, hA.skew] at h
    have : (σ η + η) * d.A.J i j = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h' | h'
    · linear_combination h'
    · exact (hij h').elim

end PositivityTheory.SiegelWeilFormula.ThetaDictR

end
