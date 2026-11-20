import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitsOfSplitOn

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Establish `hb : ∀ r : B, b (fun _ => r) = fun _ => r` using `fun r => by conv_lhs => rw [← ha r]`. Conclude with `hba _`. Set `δ : Fin d → (Fin d → B)` to `fun k => Pi.single k 1`. Establish `δmul : ∀ (k : Fin d) (x : Fin d → B), δ k * x = (fun _ => x k) * δ k`. Introduce `k x`.

Use function extensionality and compare the values at `m`. Distinguish the cases in `h : m = k`. Substitute `h` using the available equality. Simplify using `[δ, mul_comm]`. Simplify using `[δ, Pi.single_eq_of_ne h]`.

Establish `δδ : ∀ k, δ k * δ k = δ k`. Introduce `k`. Use function extensionality and compare the values at `m`. Distinguish the cases in `h : m = k`. Substitute `h` using the available equality.

Simplify using `[δ]`. Simplify using `[δ, Pi.single_eq_of_ne h]`. Establish `δort : ∀ k m, k ≠ m → δ k * δ m = 0`. Introduce `k m hkm`. Use function extensionality and compare the values at `n`.

Distinguish the cases in `h : n = k`. Substitute `h` using the available equality. Simplify using `[δ, Pi.single_eq_of_ne hkm]`. Simplify using `[δ, Pi.single_eq_of_ne h]`. Establish `δsum : ∑ k, δ k = 1`.

Use function extensionality and compare the values at `m`. Simplify using `[δ, Finset.sum_apply, Pi.single_apply]`. Set `E : Fin d → Fin d → B` to `fun i k => a (δ k) i`. Set `G : Fin d → Fin d → B` to `fun i k => b (δ i) k`. Establish `hGE : ∀ i k, G i k = E i k * G i k`.

Introduce `i k`. Establish `h1 : a (δ k) * δ i = (fun _ => E i k) * δ i`. Rewrite using `[mul_comm, δmul, mul_comm]`. Establish `h2` using `congrArg b h1`. Rewrite `h2` using `[map_mul, map_mul, hba, hb]`.

Establish `h3` using `congrFun h2 k`. Establish `h4` using `congrFun (δmul k (b (δ i))) k`. Simplify using `only [Pi.mul_apply] at h3 h4`. Simplify `h3` using `[δ, G]`. Establish `hEG : ∀ i k, E i k = G i k * E i k`.

Introduce `i k`. Establish `h1 : b (δ i) * δ k = (fun _ => G i k) * δ k`. Rewrite using `[mul_comm, δmul]`. Establish `h2` using `congrArg a h1`. Rewrite `h2` using `[map_mul, map_mul, hab, ha]`.

Establish `h3` using `congrFun h2 i`. Simplify using `only [Pi.mul_apply] at h3`. Simplify `h3` using `[δ, E]`. Establish `hEeqG : ∀ i k, E i k = G i k` using `fun i k => by`. Rewrite using `[hEG i k, mul_comm, ← hGE]`.

Establish `Eidem : ∀ i k, E i k * E i k = E i k`. Introduce `i k`. Use `congrFun (congrArg a (δδ k)) i` as an intermediate fact. Rewrite `this` using `[map_mul]`. Conclude with `this`.

Establish `Erow : ∀ i k m, k ≠ m → E i k * E i m = 0`. Introduce `i k m h`. Use `congrFun (congrArg a (δort k m h)) i` as an intermediate fact. Rewrite `this` using `[map_mul, map_zero]`. Conclude with `this`.

Establish `Ecol : ∀ i j k, i ≠ j → E i k * E j k = 0`. Introduce `i j k h`. Use `congrFun (congrArg b (δort i j h)) k` as an intermediate fact. Rewrite `this` using `[map_mul, map_zero]`. Rewrite using `[hEeqG, hEeqG]`.

Conclude with `this`. Establish `Esum : ∀ i, ∑ k, E i k = 1`. Introduce `i`. Use `congrFun (congrArg a δsum) i` as an intermediate fact. Rewrite `this` using `[map_sum, map_one, Finset.sum_apply]`.

Conclude with `this`. Establish `Emul : ∀ i k (x : Fin d → B), E i k * (a x i - x k) = 0`. Introduce `i k x`. Use `congrFun (congrArg a (δmul k x)) i` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, ha]`.

Simplify using `only [Pi.mul_apply] at this`. Express the relevant statement in the definitionally equal form `E i k * a x i = x k * E i k at this`. Rewrite using `[mul_sub, this]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun σ => ∏ i, E i (σ i), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `σ`. Express the relevant statement in the definitionally equal form `(∏ i, E i (σ i)) * (∏ i, E i (σ i)) = ∏ i, E i (σ i)`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun i _ => Eidem i _`. Introduce `σ τ hστ`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, σ i ≠ τ i := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hστ (Equiv.ext h)`. Express the relevant statement in the definitionally equal form `(∏ i, E i (σ i)) * (∏ i, E i (τ i)) = 0`.

Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (Erow i _ _ hi)`. Establish `h1 : ∏ i : Fin d, ∑ k, E i k = 1` using `by simp [Esum]`. Rewrite `h1` using `[Finset.prod_univ_sum]`. Rewrite using `[← h1]`.

Establish `hz : ∀ f ∈ Fintype.piFinset (fun _ : Fin d => (Finset.univ : Finset (Fin d))), f ∉ (Finset.univ.filter (fun f : Fin d → Fin d => Function.Bijective f)) → ∏ i, E i (f i) = 0`. Introduce `f _ hf`. Establish `hni : ¬ Function.Injective f`. Introduce `hinj`. Conclude with `hf (Finset.mem_filter.2 ⟨Finset.mem_univ _, Finite.injective_iff_bijective.1 hinj⟩)`.

Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by`. Simplify `hni` using `[Function.Injective]`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), ← Finset.mul_prod_erase (Finset.univ.erase i) _ (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ j⟩), ← mul_assoc, hij, Ecol i j _ hne, zero_mul]`. Rewrite using `[← Finset.sum_subset (by simp) hz]`. Use `Finset.sum_bij (fun σ _ => (σ : Fin d → Fin d)) (fun σ _ => ?_) (fun σ _ τ _ h => Equiv.coe_fn_injective h) (fun f hf => ?_) (fun σ _ => rfl)` and prove the remaining obligations.

Conclude with `Finset.mem_filter.2 ⟨Finset.mem_univ _, σ.bijective⟩`. Conclude with `⟨Equiv.ofBijective f (Finset.mem_filter.1 hf).2, Finset.mem_univ _, rfl⟩`. Introduce `σ i x`. Express the relevant statement in the definitionally equal form `(∏ j, E j (σ j)) * _ = 0`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), mul_comm (E i (σ i)), mul_assoc, Emul, mul_zero]`.
-/
private theorem perm_of_aut {B : Type} [CommRing B] {d : ℕ} (a b : (Fin d → B) →+* (Fin d → B))
    (hab : ∀ x, a (b x) = x) (hba : ∀ x, b (a x) = x) (ha : ∀ r : B, a (fun _ => r) = fun _ => r) :
    ∃ e : Equiv.Perm (Fin d) → B, CompleteOrthogonalIdempotents e ∧
      ∀ (σ : Equiv.Perm (Fin d)) (i : Fin d) (x : Fin d → B), e σ * (a x i - x (σ i)) = 0 := by
  classical
  have hb : ∀ r : B, b (fun _ => r) = fun _ => r := fun r => by
    conv_lhs => rw [← ha r]
    exact hba _
  let δ : Fin d → (Fin d → B) := fun k => Pi.single k 1
  have δmul : ∀ (k : Fin d) (x : Fin d → B), δ k * x = (fun _ => x k) * δ k := by
    intro k x
    funext m
    by_cases h : m = k
    · subst h; simp [δ, mul_comm]
    · simp [δ, Pi.single_eq_of_ne h]
  have δδ : ∀ k, δ k * δ k = δ k := by
    intro k
    funext m
    by_cases h : m = k
    · subst h; simp [δ]
    · simp [δ, Pi.single_eq_of_ne h]
  have δort : ∀ k m, k ≠ m → δ k * δ m = 0 := by
    intro k m hkm
    funext n
    by_cases h : n = k
    · subst h; simp [δ, Pi.single_eq_of_ne hkm]
    · simp [δ, Pi.single_eq_of_ne h]
  have δsum : ∑ k, δ k = 1 := by
    funext m
    simp [δ, Finset.sum_apply, Pi.single_apply]
  let E : Fin d → Fin d → B := fun i k => a (δ k) i
  let G : Fin d → Fin d → B := fun i k => b (δ i) k
  have hGE : ∀ i k, G i k = E i k * G i k := by
    intro i k
    have h1 : a (δ k) * δ i = (fun _ => E i k) * δ i := by
      rw [mul_comm, δmul, mul_comm]
    have h2 := congrArg b h1
    rw [map_mul, map_mul, hba, hb] at h2
    have h3 := congrFun h2 k
    have h4 := congrFun (δmul k (b (δ i))) k
    simp only [Pi.mul_apply] at h3 h4
    simpa [δ, G] using h3
  have hEG : ∀ i k, E i k = G i k * E i k := by
    intro i k
    have h1 : b (δ i) * δ k = (fun _ => G i k) * δ k := by
      rw [mul_comm, δmul]
    have h2 := congrArg a h1
    rw [map_mul, map_mul, hab, ha] at h2
    have h3 := congrFun h2 i
    simp only [Pi.mul_apply] at h3
    simpa [δ, E] using h3
  have hEeqG : ∀ i k, E i k = G i k := fun i k => by
    rw [hEG i k, mul_comm, ← hGE]
  have Eidem : ∀ i k, E i k * E i k = E i k := by
    intro i k
    have := congrFun (congrArg a (δδ k)) i
    rw [map_mul] at this
    exact this
  have Erow : ∀ i k m, k ≠ m → E i k * E i m = 0 := by
    intro i k m h
    have := congrFun (congrArg a (δort k m h)) i
    rw [map_mul, map_zero] at this
    exact this
  have Ecol : ∀ i j k, i ≠ j → E i k * E j k = 0 := by
    intro i j k h
    have := congrFun (congrArg b (δort i j h)) k
    rw [map_mul, map_zero] at this
    rw [hEeqG, hEeqG]
    exact this
  have Esum : ∀ i, ∑ k, E i k = 1 := by
    intro i
    have := congrFun (congrArg a δsum) i
    rw [map_sum, map_one, Finset.sum_apply] at this
    exact this
  have Emul : ∀ i k (x : Fin d → B), E i k * (a x i - x k) = 0 := by
    intro i k x
    have := congrFun (congrArg a (δmul k x)) i
    rw [map_mul, map_mul, ha] at this
    simp only [Pi.mul_apply] at this
    change E i k * a x i = x k * E i k at this
    rw [mul_sub, this]
    ring
  refine ⟨fun σ => ∏ i, E i (σ i), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro σ
    change (∏ i, E i (σ i)) * (∏ i, E i (σ i)) = ∏ i, E i (σ i)
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => Eidem i _
  · intro σ τ hστ
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ τ i := by
      by_contra h
      push_neg at h
      exact hστ (Equiv.ext h)
    change (∏ i, E i (σ i)) * (∏ i, E i (τ i)) = 0
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Erow i _ _ hi)
  · have h1 : ∏ i : Fin d, ∑ k, E i k = 1 := by simp [Esum]
    rw [Finset.prod_univ_sum] at h1
    rw [← h1]
    have hz : ∀ f ∈ Fintype.piFinset (fun _ : Fin d => (Finset.univ : Finset (Fin d))),
        f ∉ (Finset.univ.filter (fun f : Fin d → Fin d => Function.Bijective f)) → ∏ i, E i (f i) = 0 := by
      intro f _ hf
      have hni : ¬ Function.Injective f := by
        intro hinj
        exact hf (Finset.mem_filter.2 ⟨Finset.mem_univ _, Finite.injective_iff_bijective.1 hinj⟩)
      obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
        simpa [Function.Injective] using hni
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
        ← Finset.mul_prod_erase (Finset.univ.erase i) _ (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ j⟩),
        ← mul_assoc, hij, Ecol i j _ hne, zero_mul]
    rw [← Finset.sum_subset (by simp) hz]
    refine Finset.sum_bij (fun σ _ => (σ : Fin d → Fin d)) (fun σ _ => ?_) (fun σ _ τ _ h => Equiv.coe_fn_injective h)
      (fun f hf => ?_) (fun σ _ => rfl)
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, σ.bijective⟩
    · exact ⟨Equiv.ofBijective f (Finset.mem_filter.1 hf).2, Finset.mem_univ _, rfl⟩
  · intro σ i x
    change (∏ j, E j (σ j)) * _ = 0
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), mul_comm (E i (σ i)), mul_assoc, Emul, mul_zero]

private def pt {W : Scheme.{0}} {R : Type} [CommRing R] (m : Spec (CommRingCat.of R) ⟶ W) : Γ(W, ⊤) →+* R :=
  (m.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom

/- English proof (translation)
Establish `h` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)`. Establish `: (Spec.map (CommRingCat.ofHom f) ≫ m).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).hom = (m.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) ≫ CommRingCat.ofHom f`. Rewrite using `[Scheme.Hom.comp_appTop, Category.assoc, h, Category.assoc]`. Conclude with `congrArg CommRingCat.Hom.hom this`.
-/
private theorem pt_comp {W : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')
    (m : Spec (CommRingCat.of R) ⟶ W) : pt (Spec.map (CommRingCat.ofHom f) ≫ m) = f.comp (pt m) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
  have : (Spec.map (CommRingCat.ofHom f) ≫ m).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).hom =
      (m.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) ≫ CommRingCat.ofHom f := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, h, Category.assoc]
  exact congrArg CommRingCat.Hom.hom this

/- English proof (translation)
Apply `ext_of_isAffine` to reduce the goal to its premises. Establish `: m.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom = m'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom` using `CommRingCat.hom_ext h`. Conclude with `(cancel_mono _).1 this`.
-/
private theorem pt_inj {W : Scheme.{0}} [IsAffine W] {R : Type} [CommRing R] {m m' : Spec (CommRingCat.of R) ⟶ W}
    (h : pt m = pt m') : m = m' := by
  apply ext_of_isAffine
  have : m.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom = m'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom :=
    CommRingCat.hom_ext h
  exact (cancel_mono _).1 this

/- English proof (translation)
Take `⟨hz, hiso⟩` from `h`. Set `R : Fin m → CommRingCat` to `fun _ => CommRingCat.of B`. Use `haveI : IsIso (sigmaSpec R) := inferInstance`. Set `D : ∐ (fun _ : Fin m => Spec (CommRingCat.of B)) ⟶ pullback p x` to `Sigma.desc fun i => pullback.lift (z i) (𝟙 _) (by rw [hz i, Category.id_comp])`. Set `s : (∐ fun _ : Fin m => Spec (CommRingCat.of B)) ⟶ Spec (CommRingCat.of (Fin m → B))` to `sigmaSpec R`.

Use `haveI : IsIso s := inferInstanceAs (IsIso (sigmaSpec R))`. Establish `hs : ∀ i, Sigma.ι (fun _ : Fin m => Spec (CommRingCat.of B)) i ≫ s = Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin m => B) i))` using `fun i => ι_sigmaSpec R i`. Use `⟨hz, inv s ≫ D, inferInstance, fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hs i, Category.assoc, IsIso.hom_inv_id_assoc]`. Simplify using `[D]`.

Rewrite using `[← cancel_epi s, Category.assoc, IsIso.hom_inv_id_assoc]`. Apply `Sigma.hom_ext` to reduce the goal to its premises. Introduce `i`. Establish `h1 : CommRingCat.ofHom (Pi.ringHom fun _ : Fin m => RingHom.id B) ≫ CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin m => B) i) = 𝟙 _` using `by ext; rfl`. Rewrite using `[← Category.assoc (Sigma.ι _ i) s, hs i, ← Spec.map_comp, h1, Spec.map_id]`.

Simplify using `only [D, Sigma.ι_desc_assoc]`. Conclude with `pullback.lift_snd _ _ _`.
-/
private theorem splitOn_spec {Y Z : Scheme.{0}} (p : Z ⟶ Y) {B : Type} [CommRing B] (x : Spec (CommRingCat.of B) ⟶ Y)
    {m : ℕ} (z : Fin m → (Spec (CommRingCat.of B) ⟶ Z)) (h : SplitOn p x z) :
    ∃ (hz : ∀ i, z i ≫ p = x) (Ψ : Spec (CommRingCat.of (Fin m → B)) ⟶ pullback p x), IsIso Ψ ∧
      (∀ i, Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin m => B) i)) ≫ Ψ =
        pullback.lift (z i) (𝟙 _) (by rw [hz i, Category.id_comp])) ∧
      Ψ ≫ pullback.snd p x = Spec.map (CommRingCat.ofHom (Pi.ringHom fun _ : Fin m => RingHom.id B)) := by
  obtain ⟨hz, hiso⟩ := h
  let R : Fin m → CommRingCat := fun _ => CommRingCat.of B
  haveI : IsIso (sigmaSpec R) := inferInstance
  let D : ∐ (fun _ : Fin m => Spec (CommRingCat.of B)) ⟶ pullback p x :=
    Sigma.desc fun i => pullback.lift (z i) (𝟙 _) (by rw [hz i, Category.id_comp])
  let s : (∐ fun _ : Fin m => Spec (CommRingCat.of B)) ⟶ Spec (CommRingCat.of (Fin m → B)) := sigmaSpec R
  haveI : IsIso s := inferInstanceAs (IsIso (sigmaSpec R))
  have hs : ∀ i, Sigma.ι (fun _ : Fin m => Spec (CommRingCat.of B)) i ≫ s =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin m => B) i)) := fun i => ι_sigmaSpec R i
  refine ⟨hz, inv s ≫ D, inferInstance, fun i => ?_, ?_⟩
  · rw [← hs i, Category.assoc, IsIso.hom_inv_id_assoc]
    simp [D]
  · rw [← cancel_epi s, Category.assoc, IsIso.hom_inv_id_assoc]
    apply Sigma.hom_ext
    intro i
    have h1 : CommRingCat.ofHom (Pi.ringHom fun _ : Fin m => RingHom.id B) ≫
        CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin m => B) i) = 𝟙 _ := by
      ext; rfl
    rw [← Category.assoc (Sigma.ι _ i) s, hs i, ← Spec.map_comp, h1, Spec.map_id]
    simp only [D, Sigma.ι_desc_assoc]
    exact pullback.lift_snd _ _ _

end UpperTheory.Ru.crystallineComparison

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison in
/- English proof (translation)
Introduce `l Y T U _ hl hint y z z' hz hz' hs hs'`. Use `haveI := T.fin`. Set `B` to `Localization.Away (l : U)`. Set `j` to `awayPt l U`. Set `alg : U →+* B` to `algebraMap U B`.

Establish `halg : Function.Injective alg` using `IsLocalization.injective B (Submonoid.powers_le.2 hl)`. Use `haveI : IsAffine (pullback T.p y) := isAffine_of_isAffineHom (pullback.snd T.p y)`. Set `sec : ∀ w : Spec (CommRingCat.of U) ⟶ T.Z, w ≫ T.p = y → (Spec (CommRingCat.of U) ⟶ pullback T.p y)` to `fun w hw => pullback.lift w (𝟙 _) (by rw [hw, Category.id_comp])`. Set `q : pullback T.p (j ≫ y) ⟶ pullback T.p y` to `pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ j) (by rw [pullback.condition, Category.assoc])`. Take `⟨h1, Ψ, iΨ, hΨ, dΨ⟩` from `splitOn_spec T.p (j ≫ y) (fun i => j ≫ z i) hs`.

Take `⟨h2, Ψ', iΨ', hΨ', dΨ'⟩` from `splitOn_spec T.p (j ≫ y) (fun i => j ≫ z' i) hs'`. Set `dg` to `CommRingCat.ofHom (Pi.ringHom fun _ : Fin T.d => RingHom.id B)`. Set `a` to `Spec.preimage (Ψ' ≫ inv Ψ)`. Set `b` to `Spec.preimage (Ψ ≫ inv Ψ')`. Establish `ha : Spec.map a ≫ Ψ = Ψ'`.

Simplify using `[a, Spec.map_preimage]`. Establish `hb : Spec.map b ≫ Ψ' = Ψ`. Simplify using `[b, Spec.map_preimage]`. Establish `hab : b ≫ a = 𝟙 _`. Apply `Spec.map_injective` to reduce the goal to its premises.

Rewrite using `[Spec.map_comp, Spec.map_id, ← cancel_mono Ψ', Category.assoc, Category.id_comp, hb, ha]`. Establish `hba : a ≫ b = 𝟙 _`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, Spec.map_id, ← cancel_mono Ψ, Category.assoc, Category.id_comp, ha, hb]`. Establish `hda : dg ≫ a = dg`.

Apply `Spec.map_injective` to reduce the goal to its premises. Establish `hd : Spec.map dg = Ψ ≫ pullback.snd T.p (j ≫ y)` using `dΨ.symm`. Establish `hd' : Spec.map dg = Ψ' ≫ pullback.snd T.p (j ≫ y)` using `dΨ'.symm`. Combine the equalities or inequalities in the displayed calculation. Take `⟨e, he, hE⟩` from `perm_of_aut a.hom b.hom (fun x => congrArg (fun f => f.hom x) hab) (fun x => congrArg (fun f => f.hom x) hba) (fun r => congrArg (fun f => f.hom r) hda)`.

Set `ζ : Fin T.d → (Γ(pullback T.p y, ⊤) →+* U)` to `fun i => pt (sec (z i) (hz i))`. Set `ζ' : Fin T.d → (Γ(pullback T.p y, ⊤) →+* U)` to `fun i => pt (sec (z' i) (hz' i))`. Set `θ : Γ(pullback T.p y, ⊤) →+* (Fin T.d → B)` to `pt (Ψ ≫ q)`. Establish `hsf : ∀ w hw, sec w hw ≫ pullback.fst T.p y = w` using `fun w hw => pullback.lift_fst _ _ _`. Establish `hss : ∀ w hw, sec w hw ≫ pullback.snd T.p y = 𝟙 _` using `fun w hw => pullback.lift_snd _ _ _`.

Establish `hqf : q ≫ pullback.fst T.p y = pullback.fst _ _` using `pullback.lift_fst _ _ _`. Establish `hqs : q ≫ pullback.snd T.p y = pullback.snd _ _ ≫ j` using `pullback.lift_snd _ _ _`. Establish `hq : ∀ (w : Spec (CommRingCat.of U) ⟶ T.Z) (hw : w ≫ T.p = y) (h), pullback.lift (j ≫ w) (𝟙 _) h ≫ q = j ≫ sec w hw`. Introduce `w hw h`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, Category.assoc, hqf, hsf w hw, pullback.lift_fst]`. Rewrite using `[Category.assoc, Category.assoc, hqs, hss w hw, ← Category.assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]`. Establish `hθ : ∀ k s, θ s k = alg (ζ k s)`. Introduce `k s`. Establish `h3 : (Pi.evalRingHom (fun _ : Fin T.d => B) k).comp θ = pt (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin T.d => B) k)) ≫ Ψ ≫ q)` using `(pt_comp _ _).symm`.

Rewrite `h3` using `[← Category.assoc, hΨ k, hq _ (hz k)]`. Establish `h4 : pt (j ≫ sec (z k) (hz k)) = alg.comp (ζ k)` using `pt_comp alg _`. Conclude with `congrArg (fun f => f s) (h3.trans h4)`. Establish `hθ' : ∀ i s, a.hom (θ s) i = alg (ζ' i s)`. Introduce `i s`.

Establish `h3 : ((Pi.evalRingHom (fun _ : Fin T.d => B) i).comp a.hom).comp θ = pt (Spec.map (CommRingCat.ofHom ((Pi.evalRingHom (fun _ : Fin T.d => B) i).comp a.hom)) ≫ Ψ ≫ q)` using `(pt_comp _ _).symm`. Establish `h5 : Spec.map (CommRingCat.ofHom ((Pi.evalRingHom (fun _ : Fin T.d => B) i).comp a.hom)) = Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin T.d => B) i)) ≫ Spec.map a`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite `h3` using `[h5, Category.assoc, ← Category.assoc (Spec.map a), ha, ← Category.assoc, hΨ' i, hq _ (hz' i)]`.

Establish `h4 : pt (j ≫ sec (z' i) (hz' i)) = alg.comp (ζ' i)` using `pt_comp alg _`. Conclude with `congrArg (fun f => f s) (h3.trans h4)`. Establish `hlift : ∀ σ, ∃ u : U, alg u = e σ`. Introduce `σ`. Use `hint _ ⟨Polynomial.X ^ (1 + 1) - Polynomial.X, Polynomial.monic_X_pow_sub (lt_of_le_of_lt Polynomial.degree_X_le (by norm_num)), ?_⟩` and prove the remaining obligations.

Establish `hi : e σ * e σ = e σ` using `he.toOrthogonalIdempotents.idem σ`. Simplify using `[pow_two, hi]`. Use `choose u hu using hlift`. Use `⟨u, ?_, ?_⟩` and prove the remaining obligations. Establish `h6 : CompleteOrthogonalIdempotents (alg ∘ u)`.

Establish `: alg ∘ u = e` using `funext hu`. Rewrite using `[this]`. Conclude with `he`. Conclude with `(CompleteOrthogonalIdempotents.map_injective_iff alg halg).1 h6`. Introduce `σ V _ ρ hρ i`.

Establish `key : ∀ s, ρ (ζ' i s) = ρ (ζ (σ i) s)`. Introduce `s`. Establish `h7` using `hE σ i (θ s)`. Rewrite `h7` using `[hθ', hθ, ← hu, ← map_sub, ← map_mul]`. Establish `h8 : u σ * (ζ' i s - ζ (σ i) s) = 0` using `halg (by rw [h7, map_zero])`.

Establish `h9` using `congrArg ρ h8`. Rewrite `h9` using `[map_mul, hρ, one_mul, map_sub, map_zero]`. Conclude with `sub_eq_zero.1 h9`. Establish `h10 : Spec.map (CommRingCat.ofHom ρ) ≫ sec (z' i) (hz' i) = Spec.map (CommRingCat.ofHom ρ) ≫ sec (z (σ i)) (hz (σ i))`. Apply `pt_inj` to reduce the goal to its premises.

Rewrite using `[pt_comp, pt_comp]`. Use extensionality with `s`. Conclude with `key s`. Establish `h11` using `congrArg (· ≫ pullback.fst T.p y) h10`. Simplify using `only [Category.assoc, hsf] at h11`.

Conclude with `h11`.
-/
theorem UpperTheory.Ru.crystallineComparison.splitPerm :
    UpperTheory.Ru.crystallineComparison.SplitPerm := by
  intro l Y T U _ hl hint y z z' hz hz' hs hs'
  haveI := T.fin
  let B := Localization.Away (l : U)
  let j := awayPt l U
  let alg : U →+* B := algebraMap U B
  have halg : Function.Injective alg :=
    IsLocalization.injective B (Submonoid.powers_le.2 hl)
  haveI : IsAffine (pullback T.p y) := isAffine_of_isAffineHom (pullback.snd T.p y)
  let sec : ∀ w : Spec (CommRingCat.of U) ⟶ T.Z, w ≫ T.p = y → (Spec (CommRingCat.of U) ⟶ pullback T.p y) :=
    fun w hw => pullback.lift w (𝟙 _) (by rw [hw, Category.id_comp])
  let q : pullback T.p (j ≫ y) ⟶ pullback T.p y :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ j) (by rw [pullback.condition, Category.assoc])
  obtain ⟨h1, Ψ, iΨ, hΨ, dΨ⟩ := splitOn_spec T.p (j ≫ y) (fun i => j ≫ z i) hs
  obtain ⟨h2, Ψ', iΨ', hΨ', dΨ'⟩ := splitOn_spec T.p (j ≫ y) (fun i => j ≫ z' i) hs'
  let dg := CommRingCat.ofHom (Pi.ringHom fun _ : Fin T.d => RingHom.id B)
  let a := Spec.preimage (Ψ' ≫ inv Ψ)
  let b := Spec.preimage (Ψ ≫ inv Ψ')
  have ha : Spec.map a ≫ Ψ = Ψ' := by
    simp [a, Spec.map_preimage]
  have hb : Spec.map b ≫ Ψ' = Ψ := by
    simp [b, Spec.map_preimage]
  have hab : b ≫ a = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, ← cancel_mono Ψ', Category.assoc, Category.id_comp, hb, ha]
  have hba : a ≫ b = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, ← cancel_mono Ψ, Category.assoc, Category.id_comp, ha, hb]
  have hda : dg ≫ a = dg := by
    apply Spec.map_injective
    have hd : Spec.map dg = Ψ ≫ pullback.snd T.p (j ≫ y) := dΨ.symm
    have hd' : Spec.map dg = Ψ' ≫ pullback.snd T.p (j ≫ y) := dΨ'.symm
    calc Spec.map (dg ≫ a) = Spec.map a ≫ Ψ ≫ pullback.snd T.p (j ≫ y) := by rw [Spec.map_comp, hd]
      _ = Ψ' ≫ pullback.snd T.p (j ≫ y) := by rw [← Category.assoc, ha]
      _ = Spec.map dg := hd'.symm
  obtain ⟨e, he, hE⟩ := perm_of_aut a.hom b.hom
    (fun x => congrArg (fun f => f.hom x) hab) (fun x => congrArg (fun f => f.hom x) hba)
    (fun r => congrArg (fun f => f.hom r) hda)
  let ζ : Fin T.d → (Γ(pullback T.p y, ⊤) →+* U) := fun i => pt (sec (z i) (hz i))
  let ζ' : Fin T.d → (Γ(pullback T.p y, ⊤) →+* U) := fun i => pt (sec (z' i) (hz' i))
  let θ : Γ(pullback T.p y, ⊤) →+* (Fin T.d → B) := pt (Ψ ≫ q)
  have hsf : ∀ w hw, sec w hw ≫ pullback.fst T.p y = w := fun w hw => pullback.lift_fst _ _ _
  have hss : ∀ w hw, sec w hw ≫ pullback.snd T.p y = 𝟙 _ := fun w hw => pullback.lift_snd _ _ _
  have hqf : q ≫ pullback.fst T.p y = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hqs : q ≫ pullback.snd T.p y = pullback.snd _ _ ≫ j := pullback.lift_snd _ _ _
  have hq : ∀ (w : Spec (CommRingCat.of U) ⟶ T.Z) (hw : w ≫ T.p = y) (h),
      pullback.lift (j ≫ w) (𝟙 _) h ≫ q = j ≫ sec w hw := by
    intro w hw h
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hqf, hsf w hw, pullback.lift_fst]
    · rw [Category.assoc, Category.assoc, hqs, hss w hw, ← Category.assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]
  have hθ : ∀ k s, θ s k = alg (ζ k s) := by
    intro k s
    have h3 : (Pi.evalRingHom (fun _ : Fin T.d => B) k).comp θ =
        pt (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin T.d => B) k)) ≫ Ψ ≫ q) := (pt_comp _ _).symm
    rw [← Category.assoc, hΨ k, hq _ (hz k)] at h3
    have h4 : pt (j ≫ sec (z k) (hz k)) = alg.comp (ζ k) := pt_comp alg _
    exact congrArg (fun f => f s) (h3.trans h4)
  have hθ' : ∀ i s, a.hom (θ s) i = alg (ζ' i s) := by
    intro i s
    have h3 : ((Pi.evalRingHom (fun _ : Fin T.d => B) i).comp a.hom).comp θ =
        pt (Spec.map (CommRingCat.ofHom ((Pi.evalRingHom (fun _ : Fin T.d => B) i).comp a.hom)) ≫ Ψ ≫ q) :=
      (pt_comp _ _).symm
    have h5 : Spec.map (CommRingCat.ofHom ((Pi.evalRingHom (fun _ : Fin T.d => B) i).comp a.hom)) =
        Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin T.d => B) i)) ≫ Spec.map a := by
      rw [← Spec.map_comp]; rfl
    rw [h5, Category.assoc, ← Category.assoc (Spec.map a), ha, ← Category.assoc, hΨ' i, hq _ (hz' i)] at h3
    have h4 : pt (j ≫ sec (z' i) (hz' i)) = alg.comp (ζ' i) := pt_comp alg _
    exact congrArg (fun f => f s) (h3.trans h4)
  have hlift : ∀ σ, ∃ u : U, alg u = e σ := by
    intro σ
    refine hint _ ⟨Polynomial.X ^ (1 + 1) - Polynomial.X, Polynomial.monic_X_pow_sub (lt_of_le_of_lt Polynomial.degree_X_le (by norm_num)), ?_⟩
    have hi : e σ * e σ = e σ := he.toOrthogonalIdempotents.idem σ
    simp [pow_two, hi]
  choose u hu using hlift
  refine ⟨u, ?_, ?_⟩
  · have h6 : CompleteOrthogonalIdempotents (alg ∘ u) := by
      have : alg ∘ u = e := funext hu
      rw [this]
      exact he
    exact (CompleteOrthogonalIdempotents.map_injective_iff alg halg).1 h6
  · intro σ V _ ρ hρ i
    have key : ∀ s, ρ (ζ' i s) = ρ (ζ (σ i) s) := by
      intro s
      have h7 := hE σ i (θ s)
      rw [hθ', hθ, ← hu, ← map_sub, ← map_mul] at h7
      have h8 : u σ * (ζ' i s - ζ (σ i) s) = 0 := halg (by rw [h7, map_zero])
      have h9 := congrArg ρ h8
      rw [map_mul, hρ, one_mul, map_sub, map_zero] at h9
      exact sub_eq_zero.1 h9
    have h10 : Spec.map (CommRingCat.ofHom ρ) ≫ sec (z' i) (hz' i) =
        Spec.map (CommRingCat.ofHom ρ) ≫ sec (z (σ i)) (hz (σ i)) := by
      apply pt_inj
      rw [pt_comp, pt_comp]
      ext s
      exact key s
    have h11 := congrArg (· ≫ pullback.fst T.p y) h10
    simp only [Category.assoc, hsf] at h11
    exact h11
