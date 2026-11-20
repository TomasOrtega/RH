import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Take `⟨⟨k, hk⟩, hkeq⟩` from `QuotientGroup.mk_out_eq_mul (X.K j) g`. Rewrite using `[hkeq, (hf.1 k hk g).2]`. Distinguish the cases in `h0 : f g = 0`. Simplify using `[h0]`. Rewrite using `[mul_inv_rev, X.pl_left T (had g h0) (inv_mem hk)]`.
-/
private theorem hop_summand {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R]
    (T : Th.{u} B R) {m j : X.ι} {f : G → R} (hf : X.IsFn j f) (had : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹) (g : G)
    (x : T.H (X.q j)) :
    f (g : G ⧸ X.K j).out • X.pl T m j (g : G ⧸ X.K j).out⁻¹ x = f g • X.pl T m j g⁻¹ x := by
  obtain ⟨⟨k, hk⟩, hkeq⟩ := QuotientGroup.mk_out_eq_mul (X.K j) g
  rw [hkeq, (hf.1 k hk g).2]
  by_cases h0 : f g = 0
  · simp [h0]
  · rw [mul_inv_rev, X.pl_left T (had g h0) (inv_mem hk)]

/- English proof (translation)
Introduce `hPl hD B G _ X R _ _ T hT j f hf`. Take `⟨⟨m0, hm0j, had0⟩, hiso⟩` from `hD X T hT j f hf`. Establish `huniq : ∀ A A' : Module.End R (T.H (X.q j)), X.IsHop T j f A → X.IsHop T j f A' → A = A'`. Introduce `A A' hA hA'`. Use extensionality with `x`.

Apply `(hPl X T hT m0 j hm0j).1` to reduce the goal to its premises. Rewrite using `[hA m0 hm0j had0 x, hA' m0 hm0j had0 x]`. Take `⟨m, hmj, hnorm, hS⟩` from `X.deep j {(m0, 1)}`. Establish `hmm0 : X.K m ≤ X.K m0` using `fun u hu => by simpa using hS (m0, 1) (by simp) u hu`. Establish `had : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹` using `fun g hg => by`.

Simplify using `using (X.isAdmissibleIntegralBasisChange_one hmm0).mul (had0 g hg)`. Use `set S := hf.2.2.toFinset with hSdef`. Establish `hsub : ∀ (w : G ⧸ X.K j → T.H (X.q m)), Function.support (fun z => f z.out • w z) ⊆ (S : Set (G ⧸ X.K j))`. Introduce `w z hz`. Simplify using `only [S, Set.Finite.coe_toFinset, Set.mem_setOf_eq]`.

Introduce `h0`. Conclude with `hz (by simp [h0])`. Set `Y : T.H (X.q j) →ₗ[R] T.H (X.q m)` to `∑ z ∈ S, f z.out • X.pl T m j z.out⁻¹`. Establish `hYS : ∀ x, Y x = ∑ z ∈ S, f z.out • X.pl T m j z.out⁻¹ x`. Introduce `x`.

Simplify using `[Y, LinearMap.sum_apply]`. Establish `hY : ∀ x, Y x = ∑ᶠ z : G ⧸ X.K j, f z.out • X.pl T m j z.out⁻¹ x`. Introduce `x`. Rewrite using `[finsum_eq_sum_of_support_subset _ (hsub _), hYS]`. Establish `hinv : ∀ x, ∀ k ∈ X.K j, X.pl T m m k (Y x) = Y x`.

Introduce `x k hk`. Establish `hadk : X.admitted m m k` using `⟨X.K_le j k hk, fun u hu => hnorm k hk u hu⟩`. Establish `key : ∀ z : G ⧸ X.K j, X.pl T m m k (f z.out • X.pl T m j z.out⁻¹ x) = f (k⁻¹ • z).out • X.pl T m j (k⁻¹ • z).out⁻¹ x`. Introduce `z`. Establish `hz : k⁻¹ • z = ((k⁻¹ * z.out : G) : G ⧸ X.K j)` using `by conv_lhs => rw [← QuotientGroup.out_eq' z]`.

Both sides reduce to the same expression. Rewrite using `[hz, hop_summand X T hf had, (hf.1 k⁻¹ (inv_mem hk) z.out).1, map_smul]`. Distinguish the cases in `h0 : f z.out = 0`. Simplify using `[h0]`. Rewrite using `[X.pl_pl T hadk (had _ h0), mul_inv_rev, inv_inv]`.

Establish `hsub2 : Function.support (fun z : G ⧸ X.K j => X.pl T m m k (f z.out • X.pl T m j z.out⁻¹ x)) ⊆ (S : Set (G ⧸ X.K j))`. Introduce `z hz`. Simplify using `only [S, Set.Finite.coe_toFinset, Set.mem_setOf_eq]`. Introduce `h0`. Conclude with `hz (by simp [h0])`.

Rewrite using `[hYS, map_sum, ← finsum_eq_sum_of_support_subset _ hsub2, ← hYS, hY]`. Repeatedly rewrite using `[key]`. Conclude with `finsum_comp_equiv (MulAction.toPerm k⁻¹ : Equiv.Perm (G ⧸ X.K j)) (f := fun z : G ⧸ X.K j => f z.out • X.pl T m j z.out⁻¹ x)`. Establish `hinj` using `(hPl X T hT m j hmj).1`. Establish `hrange : ∀ x, Y x ∈ LinearMap.range (X.pl T m j 1)`.

Introduce `x`. Take `⟨w, hw⟩` from `(hPl X T hT m j hmj).2 hnorm (Y x) (hinv x)`. Conclude with `⟨w, hw⟩`. Set `A : Module.End R (T.H (X.q j))` to `(LinearEquiv.ofInjective (X.pl T m j 1) hinj).symm.toLinearMap ∘ₗ Y.codRestrict _ hrange`. Establish `hA : ∀ x, X.pl T m j 1 (A x) = Y x`.

Introduce `x`. Establish `h` using `congrArg Subtype.val ((LinearEquiv.ofInjective (X.pl T m j 1) hinj).apply_symm_apply ⟨Y x, hrange x⟩)`. Rewrite `h` using `[LinearEquiv.ofInjective_apply]`. Conclude with `h`. Establish `hex : ∃ A, X.IsHop T j f A` using `⟨A, hiso A m hmj had (fun x => by rw [hA, hY])⟩`.

Establish `hh : X.IsHop T j f (X.hecke T j f)`. Unfold `Tower.hecke`. Rewrite using `[dif_pos hex]`. Conclude with `hex.choose_spec`. Conclude with `⟨hh, fun A' hA' => huniq _ _ hA' hh⟩`.
-/
theorem UpperTheory.Gal.G3.pHopEx :
    PlInv.{u} → HopDeep.{u} → HopEx.{u} := by
  intro hPl hD B G _ X R _ _ T hT j f hf
  obtain ⟨⟨m0, hm0j, had0⟩, hiso⟩ := hD X T hT j f hf
  have huniq : ∀ A A' : Module.End R (T.H (X.q j)), X.IsHop T j f A → X.IsHop T j f A' → A = A' := by
    intro A A' hA hA'
    ext x
    apply (hPl X T hT m0 j hm0j).1
    rw [hA m0 hm0j had0 x, hA' m0 hm0j had0 x]
  obtain ⟨m, hmj, hnorm, hS⟩ := X.deep j {(m0, 1)}
  have hmm0 : X.K m ≤ X.K m0 := fun u hu => by simpa using hS (m0, 1) (by simp) u hu
  have had : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one hmm0).mul (had0 g hg)
  set S := hf.2.2.toFinset with hSdef
  have hsub : ∀ (w : G ⧸ X.K j → T.H (X.q m)),
      Function.support (fun z => f z.out • w z) ⊆ (S : Set (G ⧸ X.K j)) := by
    intro w z hz
    simp only [S, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hz (by simp [h0])
  let Y : T.H (X.q j) →ₗ[R] T.H (X.q m) := ∑ z ∈ S, f z.out • X.pl T m j z.out⁻¹
  have hYS : ∀ x, Y x = ∑ z ∈ S, f z.out • X.pl T m j z.out⁻¹ x := by
    intro x
    simp [Y, LinearMap.sum_apply]
  have hY : ∀ x, Y x = ∑ᶠ z : G ⧸ X.K j, f z.out • X.pl T m j z.out⁻¹ x := by
    intro x
    rw [finsum_eq_sum_of_support_subset _ (hsub _), hYS]
  have hinv : ∀ x, ∀ k ∈ X.K j, X.pl T m m k (Y x) = Y x := by
    intro x k hk
    have hadk : X.admitted m m k := ⟨X.K_le j k hk, fun u hu => hnorm k hk u hu⟩
    have key : ∀ z : G ⧸ X.K j, X.pl T m m k (f z.out • X.pl T m j z.out⁻¹ x) =
        f (k⁻¹ • z).out • X.pl T m j (k⁻¹ • z).out⁻¹ x := by
      intro z
      have hz : k⁻¹ • z = ((k⁻¹ * z.out : G) : G ⧸ X.K j) := by
        conv_lhs => rw [← QuotientGroup.out_eq' z]
        rfl
      rw [hz, hop_summand X T hf had, (hf.1 k⁻¹ (inv_mem hk) z.out).1, map_smul]
      by_cases h0 : f z.out = 0
      · simp [h0]
      · rw [X.pl_pl T hadk (had _ h0), mul_inv_rev, inv_inv]
    have hsub2 : Function.support (fun z : G ⧸ X.K j => X.pl T m m k (f z.out • X.pl T m j z.out⁻¹ x))
        ⊆ (S : Set (G ⧸ X.K j)) := by
      intro z hz
      simp only [S, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      intro h0
      exact hz (by simp [h0])
    rw [hYS, map_sum, ← finsum_eq_sum_of_support_subset _ hsub2, ← hYS, hY]
    simp_rw [key]
    exact finsum_comp_equiv (MulAction.toPerm k⁻¹ : Equiv.Perm (G ⧸ X.K j))
      (f := fun z : G ⧸ X.K j => f z.out • X.pl T m j z.out⁻¹ x)
  have hinj := (hPl X T hT m j hmj).1
  have hrange : ∀ x, Y x ∈ LinearMap.range (X.pl T m j 1) := by
    intro x
    obtain ⟨w, hw⟩ := (hPl X T hT m j hmj).2 hnorm (Y x) (hinv x)
    exact ⟨w, hw⟩
  let A : Module.End R (T.H (X.q j)) :=
    (LinearEquiv.ofInjective (X.pl T m j 1) hinj).symm.toLinearMap ∘ₗ Y.codRestrict _ hrange
  have hA : ∀ x, X.pl T m j 1 (A x) = Y x := by
    intro x
    have h := congrArg Subtype.val
      ((LinearEquiv.ofInjective (X.pl T m j 1) hinj).apply_symm_apply ⟨Y x, hrange x⟩)
    rw [LinearEquiv.ofInjective_apply] at h
    exact h
  have hex : ∃ A, X.IsHop T j f A := ⟨A, hiso A m hmj had (fun x => by rw [hA, hY])⟩
  have hh : X.IsHop T j f (X.hecke T j f) := by
    unfold Tower.hecke
    rw [dif_pos hex]
    exact hex.choose_spec
  exact ⟨hh, fun A' hA' => huniq _ _ hA' hh⟩
