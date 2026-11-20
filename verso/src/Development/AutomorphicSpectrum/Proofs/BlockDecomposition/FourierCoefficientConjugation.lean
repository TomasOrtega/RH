import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc GlobalTheory.CompanionTheory.FourierN
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

variable {D : D7} {n : ℕ}

/- English proof (translation)
The claim follows from `adj_mul x y`.
-/
theorem adj_mul_sq (x y : Mx D n n) : adj (x * y) = adj y * adj x := adj_mul x y

/- English proof (translation)
The claim follows from `rat_mul x y`.
-/
theorem rat_mul_sq (x y : Matrix (Fin n) (Fin n) D.host.E) : (rat (x * y) : Mx D n n) = rat x * rat y := rat_mul x y

/- English proof (translation)
The claim follows from `Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))`.
-/
theorem rat_one_sq : (rat (1 : Matrix (Fin n) (Fin n) D.host.E) : Mx D n n) = 1 :=
  Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))

/- English proof (translation)
Rewrite using `[← rat_one_sq, ← rat_conjTranspose, Matrix.conjTranspose_one]`.
-/
theorem adj_one_sq : adj (1 : Mx D n n) = 1 := by
  rw [← rat_one_sq, ← rat_conjTranspose, Matrix.conjTranspose_one]

/- English proof (translation)
Rewrite using `[← rat_mul_sq, show a.1 * (a⁻¹).1 = 1 from by simp, rat_one_sq]`.
-/
theorem rat_gl_mul_inv (a : GL (Fin n) D.host.E) : (rat a.1 * rat (a⁻¹).1 : Mx D n n) = 1 := by
  rw [← rat_mul_sq, show a.1 * (a⁻¹).1 = 1 from by simp, rat_one_sq]

/- English proof (translation)
Rewrite using `[← rat_mul_sq, show (a⁻¹).1 * a.1 = 1 from by simp, rat_one_sq]`.
-/
theorem rat_gl_inv_mul (a : GL (Fin n) D.host.E) : (rat (a⁻¹).1 * rat a.1 : Mx D n n) = 1 := by
  rw [← rat_mul_sq, show (a⁻¹).1 * a.1 = 1 from by simp, rat_one_sq]

def congH (u : Matrix (Fin n) (Fin n) D.host.E) (b : hermA D n) : hermA D n :=
  ⟨rat u * b.1 * adj (rat u), by
    show adj (rat u * b.1 * adj (rat u)) = _
    have hb : adj b.1 = b.1 := b.2
    rw [adj_mul_sq, adj_mul_sq, adj_adj, hb, mul_assoc]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem congH_val (u : Matrix (Fin n) (Fin n) D.host.E) (b : hermA D n) :
    (congH u b).1 = rat u * b.1 * adj (rat u) := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Establish `h' : (adj (rat v) * adj (rat u) : Mx D n n) = 1` using `by rw [← adj_mul_sq, h, adj_one_sq]`. Rewrite using `[congH_val, congH_val]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem congH_cancel {u v : Matrix (Fin n) (Fin n) D.host.E} (h : (rat u * rat v : Mx D n n) = 1) (b : hermA D n) :
    congH u (congH v b) = b := by
  apply Subtype.ext
  have h' : (adj (rat v) * adj (rat u) : Mx D n n) = 1 := by rw [← adj_mul_sq, h, adj_one_sq]
  rw [congH_val, congH_val]
  calc rat u * (rat v * b.1 * adj (rat v)) * adj (rat u)
      = (rat u * rat v) * b.1 * (adj (rat v) * adj (rat u)) := by simp only [mul_assoc]
    _ = b.1 := by rw [h, h', one_mul, mul_one]

/- English proof (translation)
The claim follows from `Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _`.
-/
theorem continuous_congH (u : Matrix (Fin n) (Fin n) D.host.E) : Continuous (congH (D := D) u) :=
  Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _

/- English proof (translation)
Take `⟨η, hη⟩` from `hb`. Establish `hη' : b.1 = rat η` using `hη.symm`. Use `⟨u * η * uᴴ, ?_⟩` and prove the remaining obligations. Use `show rat (u * η * uᴴ) = rat u * b.1 * adj (rat u)`. Rewrite using `[rat_mul_sq, rat_mul_sq, rat_conjTranspose, hη']`.
-/
theorem congH_rat (u : Matrix (Fin n) (Fin n) D.host.E) {b : hermA D n} (hb : b ∈ ratHerm D n) : congH u b ∈ ratHerm D n := by
  obtain ⟨η, hη⟩ := hb
  have hη' : b.1 = rat η := hη.symm
  refine ⟨u * η * uᴴ, ?_⟩
  show rat (u * η * uᴴ) = rat u * b.1 * adj (rat u)
  rw [rat_mul_sq, rat_mul_sq, rat_conjTranspose, hη']

def tauH (a : GL (Fin n) D.host.E) : hermA D n ≃ₜ+ hermA D n where
  toFun := congH (a⁻¹).1
  invFun := congH a.1
  left_inv := congH_cancel (rat_gl_mul_inv a)
  right_inv := congH_cancel (rat_gl_inv_mul a)
  map_add' b c := by
    apply Subtype.ext
    show rat (a⁻¹).1 * (b.1 + c.1) * adj (rat (a⁻¹).1) = rat (a⁻¹).1 * b.1 * adj (rat (a⁻¹).1) + rat (a⁻¹).1 * c.1 * adj (rat (a⁻¹).1)
    rw [mul_add, add_mul]
  continuous_toFun := continuous_congH _
  continuous_invFun := continuous_congH _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tauH_apply (a : GL (Fin n) D.host.E) (b : hermA D n) : tauH a b = congH (a⁻¹).1 b := rfl

/- English proof (translation)
Use `⟨fun h => ?_, fun h => congH_rat _ h⟩` and prove the remaining obligations. Use `congH_rat a.1 h` as an intermediate fact. Rewrite `this` using `[tauH_apply, congH_cancel (rat_gl_mul_inv a)]`. Then use the resulting hypothesis.
-/
theorem tauH_rat (a : GL (Fin n) D.host.E) (b : hermA D n) : tauH a b ∈ ratHerm D n ↔ b ∈ ratHerm D n := by
  refine ⟨fun h => ?_, fun h => congH_rat _ h⟩
  have := congH_rat a.1 h
  rwa [tauH_apply, congH_cancel (rat_gl_mul_inv a)] at this

/- English proof (translation)
Take `⟨q, hq⟩` from `exists_levi (D := D) (n := n) (Matrix.GeneralLinearGroup.map (incA D) a)`. Establish `hq' : mat q = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1))`. Rewrite using `[hq, ← map_inv]`. Both sides reduce to the same expression. Use `⟨q, ?_, hq'⟩` and prove the remaining obligations.

Establish `e1 : a.1 * (a⁻¹).1 = 1` using `by simp`. Establish `e2 : (a⁻¹).1 * a.1 = 1` using `by simp`. Establish `e3 : ((a⁻¹).1)ᴴ * a.1ᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]`. Establish `e4 : a.1ᴴ * ((a⁻¹).1)ᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, e2, Matrix.conjTranspose_one]`. Set `x : GL (Fin (n + n)) D.host.E` to `⟨blk4 a.1 0 0 ((a⁻¹).1)ᴴ, blk4 (a⁻¹).1 0 0 a.1ᴴ, by rw [submatrix_fromBlocks_mul]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e1, e3]; exact block_matrix_one, by rw [submatrix_fromBlocks_mul]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, …`.

Establish `hm : x.1.map (incA D) = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1))`. Simplify using `only [x, blk4_map_alt]`. Rewrite using `[Matrix.map_zero _ (map_zero _)]`. Both sides reduce to the same expression. Use `⟨x, ?_, Units.ext (hm.trans hq'.symm)⟩` and prove the remaining obligations.

Apply `rat_injective (D := D)` to reduce the goal to its premises. Establish `h2 : adj (mat q) * JR (AF D.host.F) (Jst D n) * mat q = JR (AF D.host.F) (Jst D n)` using `q.2`. Rewrite `h2` using `[hq', ← hm]`. Use `erw [rat_mul, rat_mul]`. Conclude with `h2`.
-/
theorem exists_levi_rat (a : GL (Fin n) D.host.E) :
    ∃ q : G D n, q ∈ GF D n ∧ mat q = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1)) := by
  obtain ⟨q, hq⟩ := exists_levi (D := D) (n := n) (Matrix.GeneralLinearGroup.map (incA D) a)
  have hq' : mat q = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1)) := by
    rw [hq, ← map_inv]
    rfl
  refine ⟨q, ?_, hq'⟩
  have e1 : a.1 * (a⁻¹).1 = 1 := by simp
  have e2 : (a⁻¹).1 * a.1 = 1 := by simp
  have e3 : ((a⁻¹).1)ᴴ * a.1ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
  have e4 : a.1ᴴ * ((a⁻¹).1)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e2, Matrix.conjTranspose_one]
  let x : GL (Fin (n + n)) D.host.E := ⟨blk4 a.1 0 0 ((a⁻¹).1)ᴴ, blk4 (a⁻¹).1 0 0 a.1ᴴ,
    by rw [submatrix_fromBlocks_mul]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e1, e3]; exact block_matrix_one,
    by rw [submatrix_fromBlocks_mul]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e2, e4]; exact block_matrix_one⟩
  have hm : x.1.map (incA D) = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1)) := by
    simp only [x, blk4_map_alt]
    rw [Matrix.map_zero _ (map_zero _)]
    rfl
  refine ⟨x, ?_, Units.ext (hm.trans hq'.symm)⟩
  apply rat_injective (D := D)
  have h2 : adj (mat q) * JR (AF D.host.F) (Jst D n) * mat q = JR (AF D.host.F) (Jst D n) := q.2
  rw [hq', ← hm] at h2
  erw [rat_mul, rat_mul]
  exact h2

/- English proof (translation)
Apply `GlobalTheory.CompanionTheory.FourierN.mat_injective` to reduce the goal to its premises. Use `show mat (nb b) * mat q = mat q * mat (nb (tauH a b))`. Rewrite using `[hnb, hnb, hq, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, tauH_apply, congH_val]`. Establish `e : rat a.1 * (rat (a⁻¹).1 * b.1 * adj (rat (a⁻¹).1)) = b.1 * adj (rat (a⁻¹).1)`. Rewrite using `[← mul_assoc, ← mul_assoc, rat_gl_mul_inv, one_mul]`.

Simplify using `only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e]`.
-/
theorem nb_levi {nb : hermA D n → G D n} (hnb : IsNMap nb) (a : GL (Fin n) D.host.E) {q : G D n}
    (hq : mat q = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1))) (b : hermA D n) : nb b * q = q * nb (tauH a b) := by
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  show mat (nb b) * mat q = mat q * mat (nb (tauH a b))
  rw [hnb, hnb, hq, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, tauH_apply, congH_val]
  have e : rat a.1 * (rat (a⁻¹).1 * b.1 * adj (rat (a⁻¹).1)) = b.1 * adj (rat (a⁻¹).1) := by
    rw [← mul_assoc, ← mul_assoc, rat_gl_mul_inv, one_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e]

/- English proof (translation)
Establish `h1 : ((cg a β).1.map (incA D) : Mx D n n) = adj (rat a.1) * rat β.1 * rat a.1` using `by show rat (_ * β.1 * a.1) = _`. Rewrite using `[rat_mul_sq, rat_mul_sq]`. Both sides reduce to the same expression. Establish `h2 : (adj (rat (a⁻¹).1) * adj (rat a.1) : Mx D n n) = 1` using `by rw [← adj_mul_sq, rat_gl_mul_inv, adj_one_sq]`. Use `show Matrix.trace ((cg a β).1.map (incA D) * (tauH a b).1 : Mx D n n) = Matrix.trace (rat β.1 * b.1 : Mx D n n)`.

Rewrite using `[h1, tauH_apply, congH_val]`. Establish `e : adj (rat a.1) * rat β.1 * rat a.1 * (rat (a⁻¹).1 * b.1 * adj (rat (a⁻¹).1)) = adj (rat a.1) * ((rat β.1 * b.1) * adj (rat (a⁻¹).1))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e, Matrix.trace_mul_comm, mul_assoc, h2, mul_one]`.
-/
theorem trace_cg (a : GL (Fin n) D.host.E) (β : HermE D n) (b : hermA D n) :
    Matrix.trace (HMul.hMul ((cg a β).1.map (incA D)) (tauH a b).1 : Mx D n n) =
      Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n) := by
  have h1 : ((cg a β).1.map (incA D) : Mx D n n) = adj (rat a.1) * rat β.1 * rat a.1 := by
    show rat (_ * β.1 * a.1) = _
    rw [rat_mul_sq, rat_mul_sq]
    rfl
  have h2 : (adj (rat (a⁻¹).1) * adj (rat a.1) : Mx D n n) = 1 := by rw [← adj_mul_sq, rat_gl_mul_inv, adj_one_sq]
  show Matrix.trace ((cg a β).1.map (incA D) * (tauH a b).1 : Mx D n n) = Matrix.trace (rat β.1 * b.1 : Mx D n n)
  rw [h1, tauH_apply, congH_val]
  have e : adj (rat a.1) * rat β.1 * rat a.1 * (rat (a⁻¹).1 * b.1 * adj (rat (a⁻¹).1)) =
      adj (rat a.1) * ((rat β.1 * b.1) * adj (rat (a⁻¹).1)) := by
    calc _ = adj (rat a.1) * rat β.1 * (rat a.1 * rat (a⁻¹).1) * b.1 * adj (rat (a⁻¹).1) := by simp only [mul_assoc]
      _ = _ := by rw [rat_gl_mul_inv]; simp only [mul_assoc, mul_one]
  rw [e, Matrix.trace_mul_comm, mul_assoc, h2, mul_one]

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D n ψ hψ F _ hinv nb lam 𝓖 hC a β`. Take `⟨hnb, hlam, hFD, hvol⟩` from `hC`. Take `⟨i1, i2, i3, i4, -, -⟩` from `GlobalTheory.TowerResNonzero.lattice_ratMx D n n`. Use `haveI : BorelSpace (Mx D n n) := ⟨rfl⟩`. Use `haveI : BorelSpace (hermA D n) := Subtype.borelSpace _`.

Use `haveI : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : LocallyCompactSpace (hermA D n) := isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : DiscreteTopology (ratHerm D n) := discrete_ratHerm`. Use `haveI : SecondCountableTopology (ratHerm D n) := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : Countable (ratHerm D n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance`.

Take `⟨q, hqF, hq⟩` from `exists_levi_rat (D := D) a`. Use `⟨q, fun g => ?_⟩` and prove the remaining obligations. Set `f : hermA D n → ℂ` to `fun c => F (nb c * g) * ψ (-halfTr (Matrix.trace (HMul.hMul ((cg a β).1.map (incA D)) c.1 : Mx D n n)))`. Establish `hf : ∀ γ ∈ ratHerm D n, ∀ x, f (γ + x) = f x`. Introduce `γ hγ x`.

Establish `e1 : F (nb (γ + x) * g) = F (nb x * g)`. Rewrite using `[GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]`. Conclude with `hinv _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _`. Establish `e2 : ψ (-pr (cg a β).1 (γ + x).1) = ψ (-pr (cg a β).1 x.1)`. Rewrite using `[show (γ + x).1 = γ.1 + x.1 from rfl, pr_add_right, neg_add, AddChar.map_add_eq_mul, ker_of_rat hψ γ hγ, one_mul]`.

Use `show F (nb (γ + x) * g) * ψ (-pr (cg a β).1 (γ + x).1) = F (nb x * g) * ψ (-pr (cg a β).1 x.1)`. Rewrite using `[e1, e2]`. Establish `key` using `mean_transport (ratHerm D n) (ratHerm D n) (tauH a) (tauH_rat a) lam lam hFD hFD hvol hvol f hf`. Unfold `fc`. Use `Eq.trans (integral_congr_ae (.of_forall fun b => ?_)) key` and prove the remaining obligations.

Use `show F (nb b * (q * g)) * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) = F (nb (tauH a b) * g) * ψ (-halfTr (Matrix.trace (HMul.hMul ((cg a β).1.map (incA D)) (tauH a b).1 : Mx D n n)))`. Rewrite using `[trace_cg, ← mul_assoc, nb_levi hnb a hq b, mul_assoc, hinv q hqF]`.
-/
theorem fc_levi : ∀ {D : D7} {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ F : G D n → ℂ, Continuous F →
    LeftInv (GF D n) F → ∀ {nb : hermA D n → G D n} {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)}, CoefData nb lam 𝓖 →
    ∀ (a : GL (Fin n) D.host.E) (β : HermE D n), ∃ q : G D n, ∀ g, fc ψ lam 𝓖 nb F β (q * g) = fc ψ lam 𝓖 nb F (cg a β) g := by
  intro D n ψ hψ F _ hinv nb lam 𝓖 hC a β
  obtain ⟨hnb, hlam, hFD, hvol⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (hermA D n) := isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : DiscreteTopology (ratHerm D n) := discrete_ratHerm
  haveI : SecondCountableTopology (ratHerm D n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratHerm D n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨q, hqF, hq⟩ := exists_levi_rat (D := D) a
  refine ⟨q, fun g => ?_⟩
  let f : hermA D n → ℂ := fun c =>
    F (nb c * g) * ψ (-halfTr (Matrix.trace (HMul.hMul ((cg a β).1.map (incA D)) c.1 : Mx D n n)))
  have hf : ∀ γ ∈ ratHerm D n, ∀ x, f (γ + x) = f x := by
    intro γ hγ x
    have e1 : F (nb (γ + x) * g) = F (nb x * g) := by
      rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
      exact hinv _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _
    have e2 : ψ (-pr (cg a β).1 (γ + x).1) = ψ (-pr (cg a β).1 x.1) := by
      rw [show (γ + x).1 = γ.1 + x.1 from rfl, pr_add_right, neg_add, AddChar.map_add_eq_mul, ker_of_rat hψ γ hγ, one_mul]
    show F (nb (γ + x) * g) * ψ (-pr (cg a β).1 (γ + x).1) = F (nb x * g) * ψ (-pr (cg a β).1 x.1)
    rw [e1, e2]
  have key := mean_transport (ratHerm D n) (ratHerm D n) (tauH a) (tauH_rat a) lam lam hFD hFD hvol hvol f hf
  unfold fc
  refine Eq.trans (integral_congr_ae (.of_forall fun b => ?_)) key
  show F (nb b * (q * g)) * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) =
    F (nb (tauH a b) * g) * ψ (-halfTr (Matrix.trace (HMul.hMul ((cg a β).1.map (incA D)) (tauH a b).1 : Mx D n n)))
  rw [trace_cg, ← mul_assoc, nb_levi hnb a hq b, mul_assoc, hinv q hqF]

end GlobalTheory.CompanionTheory.PcFc
