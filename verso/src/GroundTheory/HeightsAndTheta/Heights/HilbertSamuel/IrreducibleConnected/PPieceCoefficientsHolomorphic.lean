import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StPieceCoefficientsHolomorphic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Matrix Filter Topology

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `k`. Simplify using `only [Finset.prod_empty]`. Conclude with `differentiableAt_const _`.

Consider the case `insert a S ha ih`. Introduce `k`. Establish `ih'` using `ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))`. Simplify using `only [Finset.prod_insert ha, Polynomial.coeff_mul]`. Conclude with `DifferentiableAt.fun_sum fun p _ => (hP a (Finset.mem_insert_self a S) p.1).mul (ih' p.2)`.
-/
theorem coeff_finset_prod_differentiableAt {d : ℕ} {ι : Type*} (S : Finset ι)
    (P : ι → (Fin d → ℂ) → Polynomial ℂ) (y₀ : Fin d → ℂ)
    (hP : ∀ i ∈ S, ∀ k, DifferentiableAt ℂ (fun y => (P i y).coeff k) y₀) :
    ∀ k, DifferentiableAt ℂ (fun y => (∏ i ∈ S, P i y).coeff k) y₀ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro k
    simp only [Finset.prod_empty]
    exact differentiableAt_const _
  | insert a S ha ih =>
    intro k
    have ih' := ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))
    simp only [Finset.prod_insert ha, Polynomial.coeff_mul]
    exact DifferentiableAt.fun_sum fun p _ =>
      (hP a (Finset.mem_insert_self a S) p.1).mul (ih' p.2)

/- English proof (translation)
Simplify using `only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]`. Distinguish the cases in `hk : k = 0`. Substitute `hk` using the available equality. Simplify using `using ha.neg`. Simplify using `only [hk, if_false]`.

Conclude with `differentiableAt_const _`.
-/
theorem coeff_X_sub_C_differentiableAt {d : ℕ} (a : (Fin d → ℂ) → ℂ) (y₀ : Fin d → ℂ)
    (ha : DifferentiableAt ℂ a y₀) (k : ℕ) :
    DifferentiableAt ℂ (fun y => (Polynomial.X - Polynomial.C (a y)).coeff k) y₀ := by
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
  by_cases hk : k = 0
  · subst hk
    simpa using ha.neg
  · simp only [hk, if_false]
    exact differentiableAt_const _

/- English proof (translation)
Introduce `n d N A Z c Q O F hcov hO hF hXOF i y₀ hy₀`. Establish `hy₀' : eval y₀ Q ≠ 0` using `hy₀`. Take `⟨hfin, hcard, hsec⟩` from `hcov y₀ hy₀'`. Use `choose! U V g hU hyU hV hxV hg hgy hAg hZV using hsec`. Use `set T : Finset (Fin n → ℂ) := hfin.toFinset with hT`.

Establish `hmemT : ∀ x, x ∈ T ↔ x ∈ Z ∧ A *ᵥ x = y₀` using `fun x => by simp [T]`. Establish `hTcard : T.card = N` using `by rw [← hcard, Set.ncard_eq_toFinset_card _ hfin]`. Establish `hgd : ∀ x ∈ T, DifferentiableAt ℂ (g x) y₀` using `fun x hx => (hg x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2).differentiableAt ((hU x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2).mem_nhds (hyU x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2))`. Establish `hgc : ∀ x ∈ T, Tendsto (g x) (𝓝 y₀) (𝓝 x)` using `fun x hx => by`. Use `(hgd x hx).continuousAt` as an intermediate fact.

Rewrite `this` using `[ContinuousAt, hgy x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2]`. Conclude with `this`. Establish `hQopen : IsOpen {y : Fin d → ℂ | eval y Q ≠ 0}` using `isOpen_ne_fun (MvPolynomial.continuous_eval Q) continuous_const`. Establish `hev : ∀ᶠ w in 𝓝 y₀, eval w Q ≠ 0 ∧ (∀ x ∈ T, w ∈ U x) ∧ (∀ x ∈ T, ∀ x' ∈ T, x ≠ x' → g x w ≠ g x' w) ∧ (∀ x ∈ T, x ∈ O → g x w ∈ O) ∧ (∀ x ∈ T, x ∉ O → g x w ∉ F)`. Use `Filter.Eventually.and (hQopen.mem_nhds hy₀') (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_)))` and prove the remaining obligations.

Conclude with `(eventually_all_finset T).2 fun x hx => (hU x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2).mem_nhds (hyU x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2)`. Use `(eventually_all_finset T).2 fun x hx => (eventually_all_finset T).2 fun x' hx' => ?_` and prove the remaining obligations. Distinguish the cases in `hxx : x = x'`. Conclude with `Filter.Eventually.of_forall fun w h => absurd hxx h`. Conclude with `((hgc x hx).prodMk_nhds (hgc x' hx')).eventually ((isOpen_ne_fun continuous_fst continuous_snd).eventually_mem (show (x, x') ∈ {p : (Fin n → ℂ) × (Fin n → ℂ) | p.1 ≠ p.2} from hxx)) |>.mono fun w hw _ => hw`.

Use `(eventually_all_finset T).2 fun x hx => ?_` and prove the remaining obligations. Distinguish the cases in `hxO : x ∈ O`. Conclude with `((hgc x hx).eventually (hO.eventually_mem hxO)).mono fun w hw _ => hw`. Conclude with `Filter.Eventually.of_forall fun w h => absurd h hxO`. Use `(eventually_all_finset T).2 fun x hx => ?_` and prove the remaining obligations.

Distinguish the cases in `hxO : x ∈ O`. Conclude with `Filter.Eventually.of_forall fun w h => absurd hxO h`. Establish `hxF : x ∉ F`. Introduce `hxF`. Establish `hX : x ∈ {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ F` using `⟨⟨((hmemT x).1 hx).1, by rw [((hmemT x).1 hx).2]; exact hy₀'⟩, hxF⟩`.

Rewrite `hX` using `[← hXOF]`. Conclude with `hxO hX.2`. Conclude with `((hgc x hx).eventually (hF.isOpen_compl.eventually_mem hxF)).mono fun w hw _ => hw`. Establish `heq : (fun y => (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y}, (Polynomial.X - Polynomial.C (∑ j, c j * x j))).coeff i) =ᶠ[𝓝 y₀] (fun y => (∏ x ∈ T.filter (· ∈ O), (Polynomial.X - Polynomial.C (∑ j, c j * g x y j))).coeff i)` using `by filter_upwards [hev] with w ⟨hwQ, hwU, hwinj, hwO, hwF⟩`. Establish `hinj : Set.InjOn (fun x => g x w) T` using `fun x hx x' hx' h => by`.

Assume the negation of the conclusion as `hne`. Conclude with `hwinj x hx x' hx' hne h`. Establish `hgZ : ∀ x ∈ T, g x w ∈ Z ∧ A *ᵥ g x w = w` using `fun x hx => by`. Establish `h1` using `((hmemT x).1 hx).1`. Establish `h2` using `((hmemT x).1 hx).2`.

Use `⟨?_, hAg x h1 h2 w (hwU x hx)⟩` and prove the remaining obligations. Establish `hmem : g x w ∈ g x '' U x` using `⟨w, hwU x hx, rfl⟩`. Rewrite `hmem` using `[← hZV x h1 h2]`. Conclude with `hmem.1`. Take `⟨hfinw, hcardw, -⟩` from `hcov w hwQ`.

Establish `hfull : ((T.image fun x => g x w : Finset _) : Set (Fin n → ℂ)) = {x | x ∈ Z ∧ A *ᵥ x = w}`. Apply `Set.eq_of_subset_of_ncard_le _ _ hfinw` to reduce the goal to its premises. Introduce `z hz`. Simplify using `only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz`. Take `⟨x, hx, rfl⟩` from `hz`.

Conclude with `hgZ x hx`. Rewrite using `[hcardw, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, hTcard]`. Establish `hset : {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = w} = (((T.filter (· ∈ O)).image fun x => g x w : Finset _) : Set (Fin n → ℂ))`. Use extensionality with `z`. Simplify using `only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_image, Finset.mem_filter]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hzZ, hzO, hzA⟩`. Establish `hz : z ∈ ((T.image fun x => g x w : Finset _) : Set (Fin n → ℂ))`. Rewrite using `[hfull]`. Conclude with `⟨hzZ, hzA⟩`.

Simplify using `only [Finset.mem_coe, Finset.mem_image] at hz`. Take `⟨x, hx, rfl⟩` from `hz`. Use `⟨x, ⟨hx, ?_⟩, rfl⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hxO`. Establish `hX : g x w ∈ {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ O` using `⟨⟨hzZ, by rw [hzA]; exact hwQ⟩, hzO⟩`.

Rewrite `hX` using `[hXOF]`. Conclude with `hwF x hx hxO hX.2`. Introduce and unpack `⟨x, ⟨hx, hxO⟩, rfl⟩`. Conclude with `⟨(hgZ x hx).1, hwO x hx hxO, (hgZ x hx).2⟩`. Establish `key : (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = w}, (Polynomial.X - Polynomial.C (∑ j, c j * x j))) = ∏ x ∈ T.filter (· ∈ O), (Polynomial.X - Polynomial.C (∑ j, c j * g x w j))`.

Rewrite using `[hset, finprod_mem_coe_finset, Finset.prod_image (fun x hx x' hx' h => hinj (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hx').1 h)]`. Conclude with `congrArg (fun p => Polynomial.coeff p i) key`. Establish `hd : DifferentiableAt ℂ (fun y => (∏ x ∈ T.filter (· ∈ O), (Polynomial.X - Polynomial.C (∑ j, c j * g x y j))).coeff i) y₀` using `coeff_finset_prod_differentiableAt _ _ _ (fun x hx k => coeff_X_sub_C_differentiableAt _ _ (DifferentiableAt.fun_sum fun j _ => (differentiableAt_pi.1 (hgd x (Finset.mem_filter.1 hx).1) j).const_mul (c j)) k) i`. Conclude with `(hd.congr_of_eventuallyEq heq).differentiableWithinAt`.
-/
theorem PieceCoefficientsHolomorphic.proof : PieceCoefficientsHolomorphic.Statement := by
  classical
  intro n d N A Z c Q O F hcov hO hF hXOF i y₀ hy₀
  have hy₀' : eval y₀ Q ≠ 0 := hy₀
  obtain ⟨hfin, hcard, hsec⟩ := hcov y₀ hy₀'
  choose! U V g hU hyU hV hxV hg hgy hAg hZV using hsec
  set T : Finset (Fin n → ℂ) := hfin.toFinset with hT
  have hmemT : ∀ x, x ∈ T ↔ x ∈ Z ∧ A *ᵥ x = y₀ := fun x => by simp [T]
  have hTcard : T.card = N := by rw [← hcard, Set.ncard_eq_toFinset_card _ hfin]
  have hgd : ∀ x ∈ T, DifferentiableAt ℂ (g x) y₀ := fun x hx =>
    (hg x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2).differentiableAt
      ((hU x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2).mem_nhds
        (hyU x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2))
  have hgc : ∀ x ∈ T, Tendsto (g x) (𝓝 y₀) (𝓝 x) := fun x hx => by
    have := (hgd x hx).continuousAt
    rw [ContinuousAt, hgy x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2] at this
    exact this
  have hQopen : IsOpen {y : Fin d → ℂ | eval y Q ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval Q) continuous_const
  have hev : ∀ᶠ w in 𝓝 y₀, eval w Q ≠ 0 ∧ (∀ x ∈ T, w ∈ U x) ∧
      (∀ x ∈ T, ∀ x' ∈ T, x ≠ x' → g x w ≠ g x' w) ∧
      (∀ x ∈ T, x ∈ O → g x w ∈ O) ∧ (∀ x ∈ T, x ∉ O → g x w ∉ F) := by
    refine Filter.Eventually.and (hQopen.mem_nhds hy₀') (Filter.Eventually.and ?_
      (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_)))
    · exact (eventually_all_finset T).2 fun x hx =>
        (hU x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2).mem_nhds (hyU x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2)
    · refine (eventually_all_finset T).2 fun x hx => (eventually_all_finset T).2 fun x' hx' => ?_
      by_cases hxx : x = x'
      · exact Filter.Eventually.of_forall fun w h => absurd hxx h
      · exact ((hgc x hx).prodMk_nhds (hgc x' hx')).eventually
          ((isOpen_ne_fun continuous_fst continuous_snd).eventually_mem
            (show (x, x') ∈ {p : (Fin n → ℂ) × (Fin n → ℂ) | p.1 ≠ p.2} from hxx)) |>.mono
          fun w hw _ => hw
    · refine (eventually_all_finset T).2 fun x hx => ?_
      by_cases hxO : x ∈ O
      · exact ((hgc x hx).eventually (hO.eventually_mem hxO)).mono fun w hw _ => hw
      · exact Filter.Eventually.of_forall fun w h => absurd h hxO
    · refine (eventually_all_finset T).2 fun x hx => ?_
      by_cases hxO : x ∈ O
      · exact Filter.Eventually.of_forall fun w h => absurd hxO h
      · have hxF : x ∉ F := by
          intro hxF
          have hX : x ∈ {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ F :=
            ⟨⟨((hmemT x).1 hx).1, by rw [((hmemT x).1 hx).2]; exact hy₀'⟩, hxF⟩
          rw [← hXOF] at hX
          exact hxO hX.2
        exact ((hgc x hx).eventually (hF.isOpen_compl.eventually_mem hxF)).mono fun w hw _ => hw
  have heq : (fun y => (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y},
        (Polynomial.X - Polynomial.C (∑ j, c j * x j))).coeff i) =ᶠ[𝓝 y₀]
      (fun y => (∏ x ∈ T.filter (· ∈ O),
        (Polynomial.X - Polynomial.C (∑ j, c j * g x y j))).coeff i) := by
    filter_upwards [hev] with w ⟨hwQ, hwU, hwinj, hwO, hwF⟩
    have hinj : Set.InjOn (fun x => g x w) T := fun x hx x' hx' h => by
      by_contra hne
      exact hwinj x hx x' hx' hne h
    have hgZ : ∀ x ∈ T, g x w ∈ Z ∧ A *ᵥ g x w = w := fun x hx => by
      have h1 := ((hmemT x).1 hx).1
      have h2 := ((hmemT x).1 hx).2
      refine ⟨?_, hAg x h1 h2 w (hwU x hx)⟩
      have hmem : g x w ∈ g x '' U x := ⟨w, hwU x hx, rfl⟩
      rw [← hZV x h1 h2] at hmem
      exact hmem.1
    obtain ⟨hfinw, hcardw, -⟩ := hcov w hwQ
    have hfull : ((T.image fun x => g x w : Finset _) : Set (Fin n → ℂ)) =
        {x | x ∈ Z ∧ A *ᵥ x = w} := by
      apply Set.eq_of_subset_of_ncard_le _ _ hfinw
      · intro z hz
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
        obtain ⟨x, hx, rfl⟩ := hz
        exact hgZ x hx
      · rw [hcardw, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, hTcard]
    have hset : {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = w} =
        (((T.filter (· ∈ O)).image fun x => g x w : Finset _) : Set (Fin n → ℂ)) := by
      ext z
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨hzZ, hzO, hzA⟩
        have hz : z ∈ ((T.image fun x => g x w : Finset _) : Set (Fin n → ℂ)) := by
          rw [hfull]; exact ⟨hzZ, hzA⟩
        simp only [Finset.mem_coe, Finset.mem_image] at hz
        obtain ⟨x, hx, rfl⟩ := hz
        refine ⟨x, ⟨hx, ?_⟩, rfl⟩
        by_contra hxO
        have hX : g x w ∈ {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ O :=
          ⟨⟨hzZ, by rw [hzA]; exact hwQ⟩, hzO⟩
        rw [hXOF] at hX
        exact hwF x hx hxO hX.2
      · rintro ⟨x, ⟨hx, hxO⟩, rfl⟩
        exact ⟨(hgZ x hx).1, hwO x hx hxO, (hgZ x hx).2⟩
    have key : (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = w},
        (Polynomial.X - Polynomial.C (∑ j, c j * x j))) =
        ∏ x ∈ T.filter (· ∈ O), (Polynomial.X - Polynomial.C (∑ j, c j * g x w j)) := by
      rw [hset, finprod_mem_coe_finset, Finset.prod_image
        (fun x hx x' hx' h => hinj (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hx').1 h)]
    exact congrArg (fun p => Polynomial.coeff p i) key
  have hd : DifferentiableAt ℂ (fun y => (∏ x ∈ T.filter (· ∈ O),
      (Polynomial.X - Polynomial.C (∑ j, c j * g x y j))).coeff i) y₀ :=
    coeff_finset_prod_differentiableAt _ _ _ (fun x hx k => coeff_X_sub_C_differentiableAt _ _
      (DifferentiableAt.fun_sum fun j _ =>
        (differentiableAt_pi.1 (hgd x (Finset.mem_filter.1 hx).1) j).const_mul (c j)) k) i
  exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt

end GroundTheory.Heights₂.Heights.HilbertSamuel
