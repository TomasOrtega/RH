import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.ThetaDefect

/- English proof (translation)
Establish `h0 : Topology.IsEmbedding (fun n : ℤ => (n : ℂ))` using `Complex.isometry_ofReal.isEmbedding.comp Int.isClosedEmbedding_coe_real.isEmbedding`. Conclude with `h0.isDiscrete_range`.
-/
theorem isDiscrete_intRange : IsDiscrete (Set.range fun n : ℤ => (n : ℂ)) := by
  have h0 : Topology.IsEmbedding (fun n : ℤ => (n : ℂ)) :=
    Complex.isometry_ofReal.isEmbedding.comp Int.isClosedEmbedding_coe_real.isEmbedding
  exact h0.isDiscrete_range

/- English proof (translation)
The claim follows from `hS.constant_of_mapsTo isDiscrete_intRange hF (fun z hz => by obtain ⟨k, hk⟩ := hint z hz exact ⟨k, hk.symm⟩) hx hy`.
-/
theorem const_of_int {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsPreconnected S)
    {F : X → ℂ} (hF : ContinuousOn F S) (hint : ∀ x ∈ S, ∃ k : ℤ, F x = k) {x y : X}
    (hx : x ∈ S) (hy : y ∈ S) : F x = F y :=
  hS.constant_of_mapsTo isDiscrete_intRange hF (fun z hz => by
    obtain ⟨k, hk⟩ := hint z hz
    exact ⟨k, hk.symm⟩) hx hy

/- English proof (translation)
Take `⟨n, hn⟩` from `Complex.exp_eq_exp_iff_exists_int.1 h`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h2 : (2 * π * Complex.I : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero, Complex.I_ne_zero]`. Apply `mul_left_cancel₀ h2` to reduce the goal to its premises. Take the linear combination `hn`.
-/
theorem exp_eq_exp_int {a b : ℂ}
    (h : Complex.exp (2 * π * Complex.I * a) = Complex.exp (2 * π * Complex.I * b)) :
    ∃ k : ℤ, a - b = k := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  refine ⟨n, ?_⟩
  have h2 : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  apply mul_left_cancel₀ h2
  linear_combination hn

/- English proof (translation)
Establish `h : (fun i => (((x + y) (Sum.inl i) : ℝ) : ℂ)) = (fun i => (x (Sum.inl i) : ℂ)) + fun i => (y (Sum.inl i) : ℂ)`. Use extensionality with `i`. Simplify using the standard rewrite rules. Simplify using `only [per, h, Matrix.add_vecMul]`. Use extensionality with `i`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem per_add {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x y : Fl g) :
    per τ (x + y) = per τ x + per τ y := by
  have h : (fun i => (((x + y) (Sum.inl i) : ℝ) : ℂ)) =
      (fun i => (x (Sum.inl i) : ℂ)) + fun i => (y (Sum.inl i) : ℂ) := by
    ext i; simp
  simp only [per, h, Matrix.add_vecMul]
  ext i
  simp
  ring

/- English proof (translation)
Use `show (P.1, P.2 + per (τ P.1) y + per (τ P.1) x) = (P.1, P.2 + per (τ P.1) (x + y))`. Rewrite using `[per_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws.
-/
theorem transl_transl {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (x y : Fl g) (P : Pt E g) :
    transl τ x (transl τ y P) = transl τ (x + y) P := by
  show (P.1, P.2 + per (τ P.1) y + per (τ P.1) x) = (P.1, P.2 + per (τ P.1) (x + y))
  rw [per_add]
  congr 1
  abel

/- English proof (translation)
Introduce `g E _ _ B U τ hτ j hj hpol hUo hUc hUne hUB G hG`. Establish `hint : ∀ l ∈ stdLat g, ∀ i, ∃ k : ℤ, l i = k`. Introduce `l hl i`. Take `⟨k, hk⟩` from `((Pi.basisFun ℝ (Fin g ⊕ Fin g)).mem_span_iff_repr_mem ℤ l).1 hl i`. Conclude with `⟨k, by simpa using hk.symm⟩`.

Establish `hsint : ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∃ k : ℤ, (∑ i, (l (Sum.inl i) : ℂ) * (l' (Sum.inr i) : ℂ)) = k`. Introduce `l hl l' hl'`. Use `choose a ha using hint l hl`. Use `choose a' ha' using hint l' hl'`. Conclude with `⟨∑ i, a (Sum.inl i) * a' (Sum.inr i), by simp [ha, ha']⟩`.

Establish `hcovU : cov U g ⊆ cov B g` using `fun P hP => ⟨hUB hP.1, trivial⟩`. Establish `hmaps : ∀ x : Fl g, Set.MapsTo (transl τ x) (cov U g) (cov U g)` using `fun x P hP => ⟨hP.1, trivial⟩`. Establish `hτc : ∀ i k, ContinuousOn (fun P : Pt E g => τ P.1 i k) (cov U g)` using `fun i k => ((hτ.2.1 i k).continuousOn.mono hUB).comp continuousOn_fst (fun P hP => hP.1)`. Establish `hper : ∀ x : Fl g, ContinuousOn (fun P : Pt E g => per (τ P.1) x) (cov U g)`. Introduce `x`.

Use `continuousOn_pi.2 fun i => ?_` and prove the remaining obligations. Simplify using `only [per, Matrix.vecMul, dotProduct, Pi.add_apply]`. Conclude with `(continuousOn_finset_sum _ fun k _ => continuousOn_const.mul (hτc k i)).add continuousOn_const`. Establish `htc : ∀ x : Fl g, ContinuousOn (transl τ x) (cov U g)` using `fun x => continuousOn_fst.prodMk (continuousOn_snd.add (hper x))`. Establish `hpre : IsPreconnected (cov U g)` using `(hUc.prod convex_univ).isPreconnected`.

Take `⟨b₀, hb₀⟩` from `hUne`. Establish `hP₀ : ((b₀, 0) : Pt E g) ∈ cov U g` using `⟨hb₀, trivial⟩`. Establish `ha : ∀ l l' : Fl g, ∃ k : ℤ, l ∈ stdLat g → l' ∈ stdLat g → ∀ P ∈ cov U g, G (l + l') P = G l (transl τ l' P) + G l' P + k`. Introduce `l l'`. Distinguish the cases in `hl : l ∈ stdLat g`.

Use `swap`. Conclude with `⟨0, fun h => absurd h hl⟩`. Distinguish the cases in `hl' : l' ∈ stdLat g`. Use `swap`. Conclude with `⟨0, fun _ h => absurd h hl'⟩`.

Take `⟨s, hs⟩` from `hsint l hl l' hl'`. Establish `hFint : ∀ P ∈ cov U g, ∃ k : ℤ, (fun P => G (l + l') P - G l (transl τ l' P) - G l' P + s) P = k`. Introduce `P hP`. Establish `e` using `hj.2 l hl l' hl' P (hcovU hP)`. Rewrite `e` using `[(hG _ (add_mem hl hl')).2 P hP, (hG l hl).2 _ (hmaps l' hP), (hG l' hl').2 P hP, ← Complex.exp_add, ← mul_add]`.

Take `⟨k, hk⟩` from `exp_eq_exp_int e`. Establish `th : thetaExp (τ P.1) (l + l') P.2 = thetaExp (τ (transl τ l' P).1) l (transl τ l' P).2 + thetaExp (τ P.1) l' P.2 + ∑ i, (l (Sum.inl i) : ℂ) * (l' (Sum.inr i) : ℂ)` using `thetaExp_add (hτ.2.2 P.1 (hUB hP.1)).1 l l' P.2`. Conclude with `⟨k, by simp only; linear_combination hk - th - hs⟩`. Establish `hFc : ContinuousOn (fun P => G (l + l') P - G l (transl τ l' P) - G l' P + s) (cov U g)` using `((((hG _ (add_mem hl hl')).1.continuousOn).sub ((hG l hl).1.continuousOn.comp (htc l') (hmaps l'))).sub (hG l' hl').1.continuousOn).add continuousOn_const`. Take `⟨k₀, hk₀⟩` from `hFint _ hP₀`.

Use `⟨k₀ - s, fun _ _ P hP => ?_⟩` and prove the remaining obligations. Use `const_of_int hpre hFc hFint hP hP₀` as an intermediate fact. Simplify using `only at this hk₀`. Use `push_cast`. Take the linear combination `this + hk₀`.

Use `choose c hc using ha`. Use `⟨c, ?_, ?_, fun l hl l' hl' P hP => hc l l' hl hl' P hP⟩` and prove the remaining obligations. Introduce `l hl l' hl'`. Take `⟨f, hf1, hf2⟩` from `hpol b₀ (hUB hb₀)`. Establish `hsym` using `(hτ.2.2 b₀ (hUB hb₀)).1`.

Establish `hk : ∀ m ∈ stdLat g, ∀ z, f m z = thetaExp (τ b₀) m z + G m (b₀, z) + (f m 0 - thetaExp (τ b₀) m 0 - G m (b₀, 0))`. Introduce `m hm z`. Establish `hcont : ContinuousOn (fun z => f m z - thetaExp (τ b₀) m z - G m (b₀, z)) Set.univ` using `(((hf1 m hm).1.continuous.continuousOn).sub (Continuous.continuousOn (by unfold thetaExp dotProduct; fun_prop))).sub ((hG m hm).1.continuousOn.comp (Continuous.continuousOn (by fun_prop)) (fun z _ => ⟨hb₀, trivial⟩))`. Establish `hint' : ∀ z ∈ (Set.univ : Set (Fin g → ℂ)), ∃ k : ℤ, (fun z => f m z - thetaExp (τ b₀) m z - G m (b₀, z)) z = k`. Introduce `z _`.

Establish `e` using `(hf1 m hm).2 z`. Rewrite `e` using `[(hG m hm).2 (b₀, z) ⟨hb₀, trivial⟩]`. Simplify using `only at e`. Take `⟨k, hk⟩` from `exp_eq_exp_int e.symm`. Conclude with `⟨k, by simp only; linear_combination hk⟩`.

Use `const_of_int isPreconnected_univ hcont hint' (Set.mem_univ z) (Set.mem_univ 0)` as an intermediate fact. Use `beta_reduce at this`. Take the linear combination `this`. Establish `p` using `hf2 l hl l' hl' 0`. Establish `k1` using `hk l hl (0 + per (τ b₀) l')`.

Establish `k2` using `hk l' hl' 0`. Establish `k3` using `hk l' hl' (0 + per (τ b₀) l)`. Establish `k4` using `hk l hl 0`. Establish `th1` using `thetaExp_add hsym l l' 0`. Establish `th2` using `thetaExp_add hsym l' l 0`.

Rewrite `th2` using `[add_comm l' l]`. Establish `e5 : G (l + l') (b₀, 0) = G l (b₀, 0 + per (τ b₀) l') + G l' (b₀, 0) + c l l'` using `hc l l' hl hl' _ hP₀`. Establish `e6 : G (l' + l) (b₀, 0) = G l' (b₀, 0 + per (τ b₀) l) + G l (b₀, 0) + c l' l` using `hc l' l hl' hl _ hP₀`. Rewrite `e6` using `[add_comm l' l]`. Establish `e3 : (riem l l' : ℂ) = ∑ i, (l' (Sum.inl i) : ℂ) * (l (Sum.inr i) : ℂ) - ∑ i, (l (Sum.inl i) : ℂ) * (l' (Sum.inr i) : ℂ)`.

Simplify using `[riem, mul_comm]`. Establish `: (c l l' : ℂ) = c l' l`. Take the linear combination `-(p - k1 - k2 + k3 + k4 + th1 - th2 + e3 + e5 - e6)`. Conclude with `this` after adjusting the coercions. Introduce `l hl l' hl' l'' hl''`.

Establish `e1` using `hc (l + l') l'' (add_mem hl hl') hl'' _ hP₀`. Establish `e2` using `hc l l' hl hl' _ (hmaps l'' hP₀)`. Establish `e3` using `hc l (l' + l'') hl (add_mem hl' hl'') _ hP₀`. Establish `e4` using `hc l' l'' hl' hl'' _ hP₀`. Rewrite `e1` using `[add_assoc]`.

Rewrite `e2` using `[transl_transl]`. Establish `: ((c l l' + c (l + l') l'' : ℤ) : ℂ) = ((c l (l' + l'') + c l' l'' : ℤ) : ℂ)`. Use `push_cast`. Take the linear combination `e3 + e4 - e1 - e2`. Conclude with `this` after adjusting the coercions.
-/
theorem defect : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ j : Fl g → Pt E g → ℂ, IsFactor B τ (stdLat g) j → InducesPolarisation B τ (stdLat g) j → IsOpen U → Convex ℝ U → U.Nonempty → U ⊆ B → ∀ G : Fl g → Pt E g → ℂ, (∀ l ∈ stdLat g, DifferentiableOn ℂ (G l) (cov U g) ∧ ∀ P ∈ cov U g, j l P = Complex.exp (2 * π * Complex.I * (thetaExp (τ P.1) l P.2 + G l P))) → ∃ c : Fl g → Fl g → ℤ, (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, c l l' = c l' l) ∧ (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ l'' ∈ stdLat g, c l l' + c (l + l') l'' = c l (l' + l'') + c l' l'') ∧ ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov U g, G (l + l') P = G l (transl τ l' P) + G l' P + c l l' := by
  intro g E _ _ B U τ hτ j hj hpol hUo hUc hUne hUB G hG
  have hint : ∀ l ∈ stdLat g, ∀ i, ∃ k : ℤ, l i = k := by
    intro l hl i
    obtain ⟨k, hk⟩ := ((Pi.basisFun ℝ (Fin g ⊕ Fin g)).mem_span_iff_repr_mem ℤ l).1 hl i
    exact ⟨k, by simpa using hk.symm⟩
  have hsint : ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g,
      ∃ k : ℤ, (∑ i, (l (Sum.inl i) : ℂ) * (l' (Sum.inr i) : ℂ)) = k := by
    intro l hl l' hl'
    choose a ha using hint l hl
    choose a' ha' using hint l' hl'
    exact ⟨∑ i, a (Sum.inl i) * a' (Sum.inr i), by simp [ha, ha']⟩
  have hcovU : cov U g ⊆ cov B g := fun P hP => ⟨hUB hP.1, trivial⟩
  have hmaps : ∀ x : Fl g, Set.MapsTo (transl τ x) (cov U g) (cov U g) :=
    fun x P hP => ⟨hP.1, trivial⟩
  have hτc : ∀ i k, ContinuousOn (fun P : Pt E g => τ P.1 i k) (cov U g) := fun i k =>
    ((hτ.2.1 i k).continuousOn.mono hUB).comp continuousOn_fst (fun P hP => hP.1)
  have hper : ∀ x : Fl g, ContinuousOn (fun P : Pt E g => per (τ P.1) x) (cov U g) := by
    intro x
    refine continuousOn_pi.2 fun i => ?_
    simp only [per, Matrix.vecMul, dotProduct, Pi.add_apply]
    exact (continuousOn_finset_sum _ fun k _ => continuousOn_const.mul (hτc k i)).add
      continuousOn_const
  have htc : ∀ x : Fl g, ContinuousOn (transl τ x) (cov U g) := fun x =>
    continuousOn_fst.prodMk (continuousOn_snd.add (hper x))
  have hpre : IsPreconnected (cov U g) := (hUc.prod convex_univ).isPreconnected
  obtain ⟨b₀, hb₀⟩ := hUne
  have hP₀ : ((b₀, 0) : Pt E g) ∈ cov U g := ⟨hb₀, trivial⟩

  have ha : ∀ l l' : Fl g, ∃ k : ℤ, l ∈ stdLat g → l' ∈ stdLat g → ∀ P ∈ cov U g,
      G (l + l') P = G l (transl τ l' P) + G l' P + k := by
    intro l l'
    by_cases hl : l ∈ stdLat g
    swap
    · exact ⟨0, fun h => absurd h hl⟩
    by_cases hl' : l' ∈ stdLat g
    swap
    · exact ⟨0, fun _ h => absurd h hl'⟩
    obtain ⟨s, hs⟩ := hsint l hl l' hl'
    have hFint : ∀ P ∈ cov U g, ∃ k : ℤ,
        (fun P => G (l + l') P - G l (transl τ l' P) - G l' P + s) P = k := by
      intro P hP
      have e := hj.2 l hl l' hl' P (hcovU hP)
      rw [(hG _ (add_mem hl hl')).2 P hP, (hG l hl).2 _ (hmaps l' hP), (hG l' hl').2 P hP,
        ← Complex.exp_add, ← mul_add] at e
      obtain ⟨k, hk⟩ := exp_eq_exp_int e
      have th : thetaExp (τ P.1) (l + l') P.2 = thetaExp (τ (transl τ l' P).1) l (transl τ l' P).2
          + thetaExp (τ P.1) l' P.2 + ∑ i, (l (Sum.inl i) : ℂ) * (l' (Sum.inr i) : ℂ) :=
        thetaExp_add (hτ.2.2 P.1 (hUB hP.1)).1 l l' P.2
      exact ⟨k, by simp only; linear_combination hk - th - hs⟩
    have hFc : ContinuousOn (fun P => G (l + l') P - G l (transl τ l' P) - G l' P + s)
        (cov U g) :=
      ((((hG _ (add_mem hl hl')).1.continuousOn).sub
        ((hG l hl).1.continuousOn.comp (htc l') (hmaps l'))).sub
        (hG l' hl').1.continuousOn).add continuousOn_const
    obtain ⟨k₀, hk₀⟩ := hFint _ hP₀
    refine ⟨k₀ - s, fun _ _ P hP => ?_⟩
    have := const_of_int hpre hFc hFint hP hP₀
    simp only at this hk₀
    push_cast
    linear_combination this + hk₀
  choose c hc using ha
  refine ⟨c, ?_, ?_, fun l hl l' hl' P hP => hc l l' hl hl' P hP⟩
  ·
    intro l hl l' hl'
    obtain ⟨f, hf1, hf2⟩ := hpol b₀ (hUB hb₀)
    have hsym := (hτ.2.2 b₀ (hUB hb₀)).1
    have hk : ∀ m ∈ stdLat g, ∀ z, f m z = thetaExp (τ b₀) m z + G m (b₀, z) +
        (f m 0 - thetaExp (τ b₀) m 0 - G m (b₀, 0)) := by
      intro m hm z
      have hcont : ContinuousOn (fun z => f m z - thetaExp (τ b₀) m z - G m (b₀, z))
          Set.univ :=
        (((hf1 m hm).1.continuous.continuousOn).sub
          (Continuous.continuousOn (by unfold thetaExp dotProduct; fun_prop))).sub
          ((hG m hm).1.continuousOn.comp (Continuous.continuousOn (by fun_prop))
            (fun z _ => ⟨hb₀, trivial⟩))
      have hint' : ∀ z ∈ (Set.univ : Set (Fin g → ℂ)), ∃ k : ℤ,
          (fun z => f m z - thetaExp (τ b₀) m z - G m (b₀, z)) z = k := by
        intro z _
        have e := (hf1 m hm).2 z
        rw [(hG m hm).2 (b₀, z) ⟨hb₀, trivial⟩] at e
        dsimp only at e
        obtain ⟨k, hk⟩ := exp_eq_exp_int e.symm
        exact ⟨k, by simp only; linear_combination hk⟩
      have := const_of_int isPreconnected_univ hcont hint' (Set.mem_univ z) (Set.mem_univ 0)
      beta_reduce at this
      linear_combination this
    have p := hf2 l hl l' hl' 0
    have k1 := hk l hl (0 + per (τ b₀) l')
    have k2 := hk l' hl' 0
    have k3 := hk l' hl' (0 + per (τ b₀) l)
    have k4 := hk l hl 0
    have th1 := thetaExp_add hsym l l' 0
    have th2 := thetaExp_add hsym l' l 0
    rw [add_comm l' l] at th2
    have e5 : G (l + l') (b₀, 0) = G l (b₀, 0 + per (τ b₀) l') + G l' (b₀, 0) + c l l' :=
      hc l l' hl hl' _ hP₀
    have e6 : G (l' + l) (b₀, 0) = G l' (b₀, 0 + per (τ b₀) l) + G l (b₀, 0) + c l' l :=
      hc l' l hl' hl _ hP₀
    rw [add_comm l' l] at e6
    have e3 : (riem l l' : ℂ) = ∑ i, (l' (Sum.inl i) : ℂ) * (l (Sum.inr i) : ℂ) -
        ∑ i, (l (Sum.inl i) : ℂ) * (l' (Sum.inr i) : ℂ) := by
      simp [riem, mul_comm]
    have : (c l l' : ℂ) = c l' l := by
      linear_combination -(p - k1 - k2 + k3 + k4 + th1 - th2 + e3 + e5 - e6)
    exact_mod_cast this
  ·
    intro l hl l' hl' l'' hl''
    have e1 := hc (l + l') l'' (add_mem hl hl') hl'' _ hP₀
    have e2 := hc l l' hl hl' _ (hmaps l'' hP₀)
    have e3 := hc l (l' + l'') hl (add_mem hl' hl'') _ hP₀
    have e4 := hc l' l'' hl' hl'' _ hP₀
    rw [add_assoc] at e1
    rw [transl_transl] at e2
    have : ((c l l' + c (l + l') l'' : ℤ) : ℂ) = ((c l (l' + l'') + c l' l'' : ℤ) : ℂ) := by
      push_cast
      linear_combination e3 + e4 - e1 - e2
    exact_mod_cast this

end GlobalTheory.ThetaDefect
