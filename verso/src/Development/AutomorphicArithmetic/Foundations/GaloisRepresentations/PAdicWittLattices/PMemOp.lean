import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, y⟩ ⟨c', y'⟩ h`. Establish `h1 : ((c.out : G) * (y.out : G))⁻¹ * ((c'.out : G) * (y'.out : G)) ∈ U`. Use `QuotientGroup.eq.1 h` as an intermediate fact. Rewrite `this` using `[Subgroup.mem_subgroupOf]`.

Simplify using `using this`. Establish `hc : c = c'`. Rewrite using `[← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Rewrite using `[Subgroup.mem_subgroupOf]`.

Establish `e : (((c.out)⁻¹ * c'.out : K) : G) = (y.out : G) * (((c.out : G) * (y.out : G))⁻¹ * ((c'.out : G) * (y'.out : G))) * (y'.out : G)⁻¹` using `by push_cast; group`. Rewrite using `[e]`. Conclude with `V.mul_mem (V.mul_mem y.out.2 (hUV h1)) (V.inv_mem y'.out.2)`. Substitute `hc` using the available equality. Establish `hy : y = y'`.

Rewrite using `[← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Rewrite using `[Subgroup.mem_subgroupOf]`. Establish `e : (((y.out)⁻¹ * y'.out : V) : G) = ((c.out : G) * (y.out : G))⁻¹ * ((c.out : G) * (y'.out : G))` using `by push_cast; group`. Rewrite using `[e]`.

Conclude with `h1`. Rewrite using `[hy]`. Introduce `a`. Proceed by induction on `a using QuotientGroup.induction_on with`. Consider the case `H a`.

Take `⟨v, hv⟩` from `QuotientGroup.mk_out_eq_mul (V.subgroupOf K) a`. Establish `hvV : ((v : K) : G) ∈ V` using `Subgroup.mem_subgroupOf.1 v.2`. Set `b : V` to `⟨((v : K) : G)⁻¹, V.inv_mem hvV⟩`. Take `⟨w, hw⟩` from `QuotientGroup.mk_out_eq_mul (U.subgroupOf V) b`. Establish `hwU : ((w : V) : G) ∈ U` using `Subgroup.mem_subgroupOf.1 w.2`.

Use `⟨((a : K ⧸ V.subgroupOf K), (b : V ⧸ U.subgroupOf V)), ?_⟩` and prove the remaining obligations. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Rewrite using `[Subgroup.mem_subgroupOf]`. Establish `e : ((((⟨(((a : K ⧸ V.subgroupOf K).out : K) : G) * (((b : V ⧸ U.subgroupOf V).out : V) : G), K.mul_mem (a : K ⧸ V.subgroupOf K).out.2 (hVK (b : V ⧸ U.subgroupOf V).out.2)⟩ : K))⁻¹ * a : K) : G) = ((w : V) : G)⁻¹`. Simplify using `only [hv, hw, b]`.

Use `push_cast`. Use `group`. Rewrite using `[e]`. Conclude with `U.inv_mem hwU`.
-/
private theorem cos_bij {G : Type} [Group G] (K V U : Subgroup G) (hVK : V ≤ K) (hUV : U ≤ V) :
    Function.Bijective (fun p : (K ⧸ V.subgroupOf K) × (V ⧸ U.subgroupOf V) =>
      (((⟨(p.1.out : G) * (p.2.out : G), K.mul_mem p.1.out.2 (hVK p.2.out.2)⟩ : K)) : K ⧸ U.subgroupOf K)) := by
  constructor
  · rintro ⟨c, y⟩ ⟨c', y'⟩ h
    have h1 : ((c.out : G) * (y.out : G))⁻¹ * ((c'.out : G) * (y'.out : G)) ∈ U := by
      have := QuotientGroup.eq.1 h
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have hc : c = c' := by
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : (((c.out)⁻¹ * c'.out : K) : G) =
          (y.out : G) * (((c.out : G) * (y.out : G))⁻¹ * ((c'.out : G) * (y'.out : G))) * (y'.out : G)⁻¹ := by
        push_cast; group
      rw [e]
      exact V.mul_mem (V.mul_mem y.out.2 (hUV h1)) (V.inv_mem y'.out.2)
    subst hc
    have hy : y = y' := by
      rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : (((y.out)⁻¹ * y'.out : V) : G) =
          ((c.out : G) * (y.out : G))⁻¹ * ((c.out : G) * (y'.out : G)) := by
        push_cast; group
      rw [e]; exact h1
    rw [hy]
  · intro a
    induction a using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul (V.subgroupOf K) a
      have hvV : ((v : K) : G) ∈ V := Subgroup.mem_subgroupOf.1 v.2
      let b : V := ⟨((v : K) : G)⁻¹, V.inv_mem hvV⟩
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf V) b
      have hwU : ((w : V) : G) ∈ U := Subgroup.mem_subgroupOf.1 w.2
      refine ⟨((a : K ⧸ V.subgroupOf K), (b : V ⧸ U.subgroupOf V)), ?_⟩
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : ((((⟨(((a : K ⧸ V.subgroupOf K).out : K) : G) * (((b : V ⧸ U.subgroupOf V).out : V) : G),
          K.mul_mem (a : K ⧸ V.subgroupOf K).out.2 (hVK (b : V ⧸ U.subgroupOf V).out.2)⟩ : K))⁻¹ * a : K) : G) =
          ((w : V) : G)⁻¹ := by
        simp only [hv, hw, b]
        push_cast
        group
      rw [e]; exact U.inv_mem hwU

/- English proof (translation)
Introduce `hKN _ hHD hHE hTw hSum p _ D G L R _ _ gb k T N J g j F _ _ Θ hΘ f hf`. Establish `hnorm : ∀ c ∈ L.KN 1, ∀ u ∈ L.KN (g j).M.1, c * u * c⁻¹ ∈ L.KN (g j).M.1` using `fun c hc => (hKN p D G L (g j).M.1).1 c hc`. Establish `hfin : ∀ (M' : ℕ) (K' : Subgroup G.GAf), 0 < M' → K' ≤ L.KN 1 → Finite (K' ⧸ (L.KN M').subgroupOf K')`. Introduce `M' K' hM' hK'`. Establish `h1 : (L.KN M').relIndex (L.KN 1) ≠ 0` using `(hKN p D G L 1).2.2 M' one_pos hM'`.

Establish `h2 : (L.KN M').relIndex K' ≠ 0` using `fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_right hK' h0)`. Use `haveI : ((L.KN M').subgroupOf K').FiniteIndex := ⟨h2⟩`. Use `infer_instance`. Establish `hMpos : 0 < (g j).M.1` using `by have := (g j).M.2.1; omega`. Establish `hNpos : 0 < N.1` using `by have := N.2.1; omega`.

Establish `hUV : L.KN (g j).M.1 ≤ L.KN N.1` using `UpperTheory.Gal.Int.Geo.KN_anti (g j).dvd`. Establish `hV1 : L.KN N.1 ≤ L.KN 1` using `UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _)`. Use `haveI := hfin _ (g j).K hMpos (g j).le_one`. Use `haveI := hfin _ (g j).K hNpos (g j).le_one`. Use `haveI := hfin (g j).M.1 (L.KN N.1) hMpos hV1`.

Use `letI : Fintype ((g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K) := Fintype.ofFinite _`. Use `letI : Fintype ((g j).K ⧸ (L.KN N.1).subgroupOf (g j).K) := Fintype.ofFinite _`. Use `letI : Fintype (L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)) := Fintype.ofFinite _`. Establish `hadm : ∀ c ∈ (g j).K, T.X.admitted (T.lev (g j).M) (T.lev N) ((g j).h * c)` using `fun c hc => ⟨(T.Δ_eq _).2 ((g j).int.mul (UpperTheory.Gal.Int.Geo.integ_of_mem ((g j).le_one hc))), fun u hu => by`. Rewrite `hu`, the goal using `[T.K_eq]`.

Conclude with `(g j).adm c hc u hu⟩`. Establish `hmem : ∀ c ∈ (g j).K, ∀ u ∈ L.KN (g j).M.1, ∀ y, (g j).h * (c * u) * y ∈ L.KN N.1 ↔ (g j).h * c * y ∈ L.KN N.1`. Introduce `c hc u hu y`. Establish `e : (g j).h * (c * u) * y = ((g j).h * c * u * ((g j).h * c)⁻¹) * ((g j).h * c * y)` using `by group`. Rewrite using `[e]`.

Conclude with `Subgroup.mul_mem_cancel_left _ ((g j).adm c hc u hu)`. Establish `hpl : ∀ c ∈ (g j).K, ∀ u ∈ L.KN (g j).M.1, ∀ x, T.X.pl Θ (T.lev (g j).M) (T.lev N) ((g j).h * (c * u)) x = T.X.pl Θ (T.lev (g j).M) (T.lev N) ((g j).h * c) x`. Introduce `c hc u hu x`. Establish `e : (g j).h * (c * u) = ((g j).h * c * u * ((g j).h * c)⁻¹) * ((g j).h * c)` using `by group`. Rewrite using `[e]`.

Conclude with `T.X.pl_left Θ (hadm c hc) (by rw [T.K_eq]; exact (g j).adm c hc u hu) x`. Establish `hS` using `hSum T.X Θ (T.lev (g j).M) (T.lev N) ((g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K) (fun a => (g j).h * (a.out : G.GAf)) (fun a => hadm _ a.out.2) f (fun y => by rw [hf y, T.K_eq])`. Establish `hinv : ∀ k ∈ T.X.K (T.lev N), ∀ y, f (k * y) = f y`. Introduce `k₀ hk₀ y`. Rewrite `hk₀` using `[T.K_eq]`.

Establish `hk₀K : k₀ ∈ (g j).K` using `(g j).le hk₀`. Set `σ : ((g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K) → ((g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K)` to `fun a => ((a.out * ⟨k₀, hk₀K⟩ : (g j).K) : (g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K)`. Establish `hσ : Function.Injective σ`. Introduce `a b hab`. Establish `h1` using `QuotientGroup.eq.1 hab`.

Rewrite `h1` using `[Subgroup.mem_subgroupOf]`. Rewrite using `[← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Rewrite using `[Subgroup.mem_subgroupOf]`. Establish `e : (((a.out)⁻¹ * b.out : (g j).K) : G.GAf) = k₀ * ((((a.out * ⟨k₀, hk₀K⟩ : (g j).K))⁻¹ * (b.out * ⟨k₀, hk₀K⟩) : (g j).K) : G.GAf) * k₀⁻¹` using `by push_cast; group`.

Rewrite using `[e]`. Conclude with `hnorm k₀ (hV1 hk₀) _ h1`. Establish `hσb : Function.Bijective σ` using `Finite.injective_iff_bijective.1 hσ`. Establish `hcard : Nat.card {a : (g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K // (g j).h * (a.out : G.GAf) * (k₀ * y) ∈ L.KN N.1} = Nat.card {a : (g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K // (g j).h * (a.out : G.GAf) * y ∈ L.KN N.1}`. Use `Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective σ hσb) fun a => ?_)` and prove the remaining obligations.

Take `⟨w, hw⟩` from `QuotientGroup.mk_out_eq_mul ((L.KN (g j).M.1).subgroupOf (g j).K) (a.out * ⟨k₀, hk₀K⟩)`. Establish `hwU : ((w : (g j).K) : G.GAf) ∈ L.KN (g j).M.1` using `Subgroup.mem_subgroupOf.1 w.2`. Establish `e : (σ a).out = a.out * ⟨k₀, hk₀K⟩ * w` using `hw`. Establish `e2 : (((Equiv.ofBijective σ hσb) a).out : G.GAf) = (a.out : G.GAf) * k₀ * ((w : (g j).K) : G.GAf)`. Simplify using `[e]`.

Rewrite using `[e2, hmem _ ((g j).K.mul_mem a.out.2 hk₀K) _ hwU y]`. Simplify using `only [_root_.mul_assoc]`. Rewrite using `[hf, hf, hcard]`. Establish `hIsFn` using `hS.2.1 hinv`. Establish `hle : T.X.K (T.lev (g j).M) ≤ T.X.K (T.lev N)`.

Rewrite using `[T.K_eq, T.K_eq]`. Conclude with `hUV`. Use `⟨hIsFn, fun tr htr => ?_⟩` and prove the remaining obligations. Use `(hHE T.X Θ hΘ (T.lev N) f hIsFn).2 _ ((hHD T.X Θ hΘ (T.lev N) f hIsFn).2 _ (T.lev (g j).M) hle hS.1 fun x => ?_)` and prove the remaining obligations. Rewrite using `[← hS.2.2 x]`.

Establish `hU' : ∀ y : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1), ((y.out : L.KN N.1) : G.GAf) ∈ T.X.K (T.lev N)`. Introduce `y`. Rewrite using `[T.K_eq]`. Conclude with `y.out.2`. Establish `hex : ∀ k ∈ T.X.K (T.lev N), ∃! y : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1), k * ((y.out : L.KN N.1) : G.GAf)⁻¹ ∈ T.X.K (T.lev (g j).M)`.

Introduce `k hk`. Rewrite `hk` using `[T.K_eq]`. Simplify using `only [T.K_eq]`. Take `⟨w, hw⟩` from `QuotientGroup.mk_out_eq_mul ((L.KN (g j).M.1).subgroupOf (L.KN N.1)) ⟨k, hk⟩`. Establish `hwU : ((w : L.KN N.1) : G.GAf) ∈ L.KN (g j).M.1` using `Subgroup.mem_subgroupOf.1 w.2`.

Use `⟨((⟨k, hk⟩ : L.KN N.1) : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)), ?_, fun y' hy' => ?_⟩` and prove the remaining obligations. Establish `e : k * ((((⟨k, hk⟩ : L.KN N.1) : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)).out : L.KN N.1) : G.GAf)⁻¹ = k * ((w : L.KN N.1) : G.GAf)⁻¹ * k⁻¹`. Rewrite using `[hw]`. Use `push_cast`. Use `group`.

Use `show k * ((((⟨k, hk⟩ : L.KN N.1) : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)).out : L.KN N.1) : G.GAf)⁻¹ ∈ _`. Rewrite using `[e]`. Conclude with `hnorm k (hV1 hk) _ ((L.KN (g j).M.1).inv_mem hwU)`. Rewrite using `[← QuotientGroup.out_eq' y']`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations.

Rewrite using `[Subgroup.mem_subgroupOf]`. Establish `e : ((y'.out⁻¹ * ⟨k, hk⟩ : L.KN N.1) : G.GAf) = ((y'.out : L.KN N.1) : G.GAf)⁻¹ * (k * ((y'.out : L.KN N.1) : G.GAf)⁻¹) * ((y'.out : L.KN N.1) : G.GAf)⁻¹⁻¹` using `by push_cast; group`. Rewrite using `[e]`. Conclude with `hnorm _ (hV1 ((L.KN N.1).inv_mem y'.out.2)) _ hy'`. Establish `hTw'` using `hTw T.X Θ (T.lev (g j).M) (T.lev (g j).M) (T.lev N) (T.X.isAdmissibleIntegralBasisChange_one hle) le_rfl (fun k hk u hu => by`.

Rewrite `hk`, `hu`, the goal using `[T.K_eq]`. Conclude with `hnorm k (hV1 hk) u hu)`. Use the proof step `((g j).K ⧸ (L.KN N.1).subgroupOf (g j).K) (L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1))`. Use the proof step `(fun c => (g j).h * (c.out : G.GAf)) (fun c => hadm _ c.out.2)`. Use the proof step `(fun y => ((y.out : L.KN N.1) : G.GAf)) hU' hex ((T.tower N g).comm j) tr htr x`.

Use `Eq.trans hTw' ?_` and prove the remaining obligations. Use `(Fintype.sum_prod_type' (fun (c : (g j).K ⧸ (L.KN N.1).subgroupOf (g j).K) (y : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)) => T.X.pl Θ (T.lev (g j).M) (T.lev N) ((g j).h * (c.out : G.GAf) * ((y.out : L.KN N.1) : G.GAf)) x)).symm.trans ?_` and prove the remaining obligations. Use `Fintype.sum_bijective _ (cos_bij (g j).K (L.KN N.1) (L.KN (g j).M.1) (g j).le hUV) _ _ fun q => ?_` and prove the remaining obligations. Take `⟨c, y⟩` from `q`. Establish `hcy : (c.out : G.GAf) * ((y.out : L.KN N.1) : G.GAf) ∈ (g j).K` using `(g j).K.mul_mem c.out.2 ((g j).le y.out.2)`.

Take `⟨w, hw⟩` from `QuotientGroup.mk_out_eq_mul ((L.KN (g j).M.1).subgroupOf (g j).K) ⟨_, hcy⟩`. Establish `hwU : ((w : (g j).K) : G.GAf) ∈ L.KN (g j).M.1` using `Subgroup.mem_subgroupOf.1 w.2`. Simplify using `only`. Rewrite using `[hw]`. Use `push_cast`.

Rewrite using `[hpl _ hcy _ hwU x, _root_.mul_assoc]`.
-/
theorem UpperTheory.Gal.G3.pMemOp :
    KNBasic → PlInv.{u} → HopDeep.{u} → HopEx.{u} → TwMem.{u} → SumFn.{u} → MemOp.{u} := by
  intro hKN _ hHD hHE hTw hSum p _ D G L R _ _ gb k T N J g j F _ _ Θ hΘ f hf
  classical
  have hnorm : ∀ c ∈ L.KN 1, ∀ u ∈ L.KN (g j).M.1, c * u * c⁻¹ ∈ L.KN (g j).M.1 :=
    fun c hc => (hKN p D G L (g j).M.1).1 c hc
  have hfin : ∀ (M' : ℕ) (K' : Subgroup G.GAf), 0 < M' → K' ≤ L.KN 1 → Finite (K' ⧸ (L.KN M').subgroupOf K') := by
    intro M' K' hM' hK'
    have h1 : (L.KN M').relIndex (L.KN 1) ≠ 0 := (hKN p D G L 1).2.2 M' one_pos hM'
    have h2 : (L.KN M').relIndex K' ≠ 0 := fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_right hK' h0)
    haveI : ((L.KN M').subgroupOf K').FiniteIndex := ⟨h2⟩
    infer_instance
  have hMpos : 0 < (g j).M.1 := by have := (g j).M.2.1; omega
  have hNpos : 0 < N.1 := by have := N.2.1; omega
  have hUV : L.KN (g j).M.1 ≤ L.KN N.1 := UpperTheory.Gal.Int.Geo.KN_anti (g j).dvd
  have hV1 : L.KN N.1 ≤ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _)
  haveI := hfin _ (g j).K hMpos (g j).le_one
  haveI := hfin _ (g j).K hNpos (g j).le_one
  haveI := hfin (g j).M.1 (L.KN N.1) hMpos hV1
  letI : Fintype ((g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K) := Fintype.ofFinite _
  letI : Fintype ((g j).K ⧸ (L.KN N.1).subgroupOf (g j).K) := Fintype.ofFinite _
  letI : Fintype (L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)) := Fintype.ofFinite _
  have hadm : ∀ c ∈ (g j).K, T.X.admitted (T.lev (g j).M) (T.lev N) ((g j).h * c) := fun c hc =>
    ⟨(T.Δ_eq _).2 ((g j).int.mul (UpperTheory.Gal.Int.Geo.integ_of_mem ((g j).le_one hc))), fun u hu => by
      rw [T.K_eq] at hu ⊢
      exact (g j).adm c hc u hu⟩
  have hmem : ∀ c ∈ (g j).K, ∀ u ∈ L.KN (g j).M.1, ∀ y,
      (g j).h * (c * u) * y ∈ L.KN N.1 ↔ (g j).h * c * y ∈ L.KN N.1 := by
    intro c hc u hu y
    have e : (g j).h * (c * u) * y = ((g j).h * c * u * ((g j).h * c)⁻¹) * ((g j).h * c * y) := by group
    rw [e]
    exact Subgroup.mul_mem_cancel_left _ ((g j).adm c hc u hu)
  have hpl : ∀ c ∈ (g j).K, ∀ u ∈ L.KN (g j).M.1, ∀ x,
      T.X.pl Θ (T.lev (g j).M) (T.lev N) ((g j).h * (c * u)) x = T.X.pl Θ (T.lev (g j).M) (T.lev N) ((g j).h * c) x := by
    intro c hc u hu x
    have e : (g j).h * (c * u) = ((g j).h * c * u * ((g j).h * c)⁻¹) * ((g j).h * c) := by group
    rw [e]
    exact T.X.pl_left Θ (hadm c hc) (by rw [T.K_eq]; exact (g j).adm c hc u hu) x
  have hS := hSum T.X Θ (T.lev (g j).M) (T.lev N) ((g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K)
    (fun a => (g j).h * (a.out : G.GAf)) (fun a => hadm _ a.out.2) f (fun y => by rw [hf y, T.K_eq])
  have hinv : ∀ k ∈ T.X.K (T.lev N), ∀ y, f (k * y) = f y := by
    intro k₀ hk₀ y
    rw [T.K_eq] at hk₀
    have hk₀K : k₀ ∈ (g j).K := (g j).le hk₀
    let σ : ((g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K) → ((g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K) :=
      fun a => ((a.out * ⟨k₀, hk₀K⟩ : (g j).K) : (g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K)
    have hσ : Function.Injective σ := by
      intro a b hab
      have h1 := QuotientGroup.eq.1 hab
      rw [Subgroup.mem_subgroupOf] at h1
      rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : (((a.out)⁻¹ * b.out : (g j).K) : G.GAf) = k₀ *
          ((((a.out * ⟨k₀, hk₀K⟩ : (g j).K))⁻¹ * (b.out * ⟨k₀, hk₀K⟩) : (g j).K) : G.GAf) * k₀⁻¹ := by
        push_cast; group
      rw [e]
      exact hnorm k₀ (hV1 hk₀) _ h1
    have hσb : Function.Bijective σ := Finite.injective_iff_bijective.1 hσ
    have hcard : Nat.card {a : (g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K // (g j).h * (a.out : G.GAf) * (k₀ * y) ∈ L.KN N.1} =
        Nat.card {a : (g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K // (g j).h * (a.out : G.GAf) * y ∈ L.KN N.1} := by
      refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective σ hσb) fun a => ?_)
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul ((L.KN (g j).M.1).subgroupOf (g j).K) (a.out * ⟨k₀, hk₀K⟩)
      have hwU : ((w : (g j).K) : G.GAf) ∈ L.KN (g j).M.1 := Subgroup.mem_subgroupOf.1 w.2
      have e : (σ a).out = a.out * ⟨k₀, hk₀K⟩ * w := hw
      have e2 : (((Equiv.ofBijective σ hσb) a).out : G.GAf) = (a.out : G.GAf) * k₀ * ((w : (g j).K) : G.GAf) := by
        simp [e]
      rw [e2, hmem _ ((g j).K.mul_mem a.out.2 hk₀K) _ hwU y]
      simp only [_root_.mul_assoc]
    rw [hf, hf, hcard]
  have hIsFn := hS.2.1 hinv
  have hle : T.X.K (T.lev (g j).M) ≤ T.X.K (T.lev N) := by
    rw [T.K_eq, T.K_eq]; exact hUV
  refine ⟨hIsFn, fun tr htr => ?_⟩
  refine (hHE T.X Θ hΘ (T.lev N) f hIsFn).2 _ ((hHD T.X Θ hΘ (T.lev N) f hIsFn).2 _ (T.lev (g j).M) hle hS.1 fun x => ?_)
  rw [← hS.2.2 x]
  have hU' : ∀ y : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1), ((y.out : L.KN N.1) : G.GAf) ∈ T.X.K (T.lev N) := by
    intro y; rw [T.K_eq]; exact y.out.2
  have hex : ∀ k ∈ T.X.K (T.lev N), ∃! y : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1),
      k * ((y.out : L.KN N.1) : G.GAf)⁻¹ ∈ T.X.K (T.lev (g j).M) := by
    intro k hk
    rw [T.K_eq] at hk
    simp only [T.K_eq]
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul ((L.KN (g j).M.1).subgroupOf (L.KN N.1)) ⟨k, hk⟩
    have hwU : ((w : L.KN N.1) : G.GAf) ∈ L.KN (g j).M.1 := Subgroup.mem_subgroupOf.1 w.2
    refine ⟨((⟨k, hk⟩ : L.KN N.1) : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)), ?_, fun y' hy' => ?_⟩
    · have e : k * ((((⟨k, hk⟩ : L.KN N.1) : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)).out : L.KN N.1) : G.GAf)⁻¹ =
          k * ((w : L.KN N.1) : G.GAf)⁻¹ * k⁻¹ := by
        rw [hw]; push_cast; group
      show k * ((((⟨k, hk⟩ : L.KN N.1) : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)).out : L.KN N.1) : G.GAf)⁻¹ ∈ _
      rw [e]
      exact hnorm k (hV1 hk) _ ((L.KN (g j).M.1).inv_mem hwU)
    · rw [← QuotientGroup.out_eq' y']
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : ((y'.out⁻¹ * ⟨k, hk⟩ : L.KN N.1) : G.GAf) =
          ((y'.out : L.KN N.1) : G.GAf)⁻¹ * (k * ((y'.out : L.KN N.1) : G.GAf)⁻¹) * ((y'.out : L.KN N.1) : G.GAf)⁻¹⁻¹ := by
        push_cast; group
      rw [e]
      exact hnorm _ (hV1 ((L.KN N.1).inv_mem y'.out.2)) _ hy'
  have hTw' := hTw T.X Θ (T.lev (g j).M) (T.lev (g j).M) (T.lev N) (T.X.isAdmissibleIntegralBasisChange_one hle) le_rfl
    (fun k hk u hu => by
      rw [T.K_eq] at hk hu ⊢
      exact hnorm k (hV1 hk) u hu)
    ((g j).K ⧸ (L.KN N.1).subgroupOf (g j).K) (L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1))
    (fun c => (g j).h * (c.out : G.GAf)) (fun c => hadm _ c.out.2)
    (fun y => ((y.out : L.KN N.1) : G.GAf)) hU' hex ((T.tower N g).comm j) tr htr x
  refine Eq.trans hTw' ?_
  refine (Fintype.sum_prod_type' (fun (c : (g j).K ⧸ (L.KN N.1).subgroupOf (g j).K)
    (y : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)) =>
      T.X.pl Θ (T.lev (g j).M) (T.lev N) ((g j).h * (c.out : G.GAf) * ((y.out : L.KN N.1) : G.GAf)) x)).symm.trans ?_
  refine Fintype.sum_bijective _ (cos_bij (g j).K (L.KN N.1) (L.KN (g j).M.1) (g j).le hUV) _ _ fun q => ?_
  obtain ⟨c, y⟩ := q
  have hcy : (c.out : G.GAf) * ((y.out : L.KN N.1) : G.GAf) ∈ (g j).K := (g j).K.mul_mem c.out.2 ((g j).le y.out.2)
  obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul ((L.KN (g j).M.1).subgroupOf (g j).K) ⟨_, hcy⟩
  have hwU : ((w : (g j).K) : G.GAf) ∈ L.KN (g j).M.1 := Subgroup.mem_subgroupOf.1 w.2
  dsimp only
  rw [hw]
  push_cast
  rw [hpl _ hcy _ hwU x, _root_.mul_assoc]
