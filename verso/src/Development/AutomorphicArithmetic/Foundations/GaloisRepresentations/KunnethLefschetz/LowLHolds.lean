import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.H0LimitCoherence

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace LateralTheory.EtaleTrace.H0LimitCoherence
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

/- English proof (translation)
Establish `hx : ∀ x : Hl l E n 0, x = 0`. Introduce `x`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Conclude with `@Subsingleton.elim _ (h j) _ _`.

Use `⟨fun z w => ?_⟩` and prove the remaining obligations. Take `⟨b, x, -, rfl⟩` from `tensor_form l z`. Take `⟨c, y, -, rfl⟩` from `tensor_form l w`. Rewrite using `[hx x, hx y, TensorProduct.tmul_zero, TensorProduct.tmul_zero]`.
-/
private theorem sub_of (l : ℕ) [Fact l.Prime] {E : Spc} {n : ℤ} (h : ∀ j, Subsingleton (Ht (l ^ j) E n 0)) :
    Subsingleton (HQ l E n 0) := by
  have hx : ∀ x : Hl l E n 0, x = 0 := by
    intro x
    apply Subtype.ext
    funext j
    exact @Subsingleton.elim _ (h j) _ _
  refine ⟨fun z w => ?_⟩
  obtain ⟨b, x, -, rfl⟩ := tensor_form l z
  obtain ⟨c, y, -, rfl⟩ := tensor_form l w
  rw [hx x, hx y, TensorProduct.tmul_zero, TensorProduct.tmul_zero]

/- English proof (translation)
Introduce `hI hP l _ k _ _ hl hR hT`. Establish `hu : IsUnit ((l : ℕ) : Γ(S k, ⊤))`. Simplify using `using (isUnit_iff_ne_zero.mpr hl).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom`. Take `⟨ω, hω, hone⟩` from `hR.one_def (S k) hu`. Take `⟨hsurj, hinj⟩` from `rep_of ω (fun j z => by`.

Take `⟨a, ha⟩` from `(hT j).1.1 z`. Conclude with `⟨a, by rw [ha]; simp [lv, hω]⟩)`. Use the proof step `(fun j a ha => (hT j).1.2 a (by simpa [lv, hω] using ha))`. Set `e : ℤ_[l] ≃ₗ[ℤ_[l]] Hl l (sch.obj (S k)) 0 0` to `LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[l] _ ω) ⟨fun c d hcd => by`. Establish `h0 : (c - d) • ω = 0`.

Simplify `hcd` using `[sub_smul, sub_eq_zero]`. Conclude with `sub_eq_zero.mp (hinj _ h0),`. Use `fun x => by`. Take `⟨c, hc⟩` from `hsurj x`. Conclude with `⟨c, by simp [hc]⟩⟩`.

Set `Φ : V l (S k) 0 ≃ₗ[ℤ_[l]] ℚ_[l]` to `(TensorProduct.congr (LinearEquiv.refl ℤ_[l] ℚ_[l]) e.symm).trans (TensorProduct.rid ℤ_[l] ℚ_[l])`. Establish `hΦ : ∀ (q : ℚ_[l]) (u : Hl l (sch.obj (S k)) 0 0), Φ (q ⊗ₜ u) = ((e.symm u : ℤ_[l]) : ℚ_[l]) * q`. Introduce `q u`. Simplify using `[Φ, Algebra.smul_def]`. Establish `he : ∀ c : ℤ_[l], e.symm (c • ω) = c`.

Introduce `c`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Establish `hsm : ∀ r : ℚ_[l], r • oneV l (S k) = r ⊗ₜ ω`. Introduce `r`.

Rewrite using `[hone, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Establish `hΦr : ∀ r : ℚ_[l], Φ (r • oneV l (S k)) = r`. Introduce `r`. Rewrite using `[hsm, hΦ]`. Use `he 1` as an intermediate fact.

Rewrite `this` using `[one_smul]`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `key : ∀ (b : ℤ_[l]) (u : Hl l (sch.obj (S k)) 0 0), b ≠ 0 → ((b : ℚ_[l])⁻¹ ⊗ₜ[ℤ_[l]] u : V l (S k) 0) = 0 → u = 0`. Introduce `b u hb h`.

Establish `h1` using `congrArg Φ h`. Rewrite `h1` using `[hΦ, map_zero]`. Establish `hb' : (b : ℚ_[l]) ≠ 0` using `fun h' => hb (Subtype.ext h')`. Establish `h2 : ((e.symm u : ℤ_[l]) : ℚ_[l]) = 0`. Break down `mul_eq_zero.mp h1 with h3 | h3` into its components or cases.

Conclude with `h3`. Conclude with `absurd h3 (inv_ne_zero hb')`. Establish `h4 : e.symm u = 0` using `Subtype.ext h2`. Simplify using `using congrArg e h4`. Establish `hpb : ∀ {X : Scheme} (y : S k ⟶ X) (q : ℚ_[l]) (x : Hl l (sch.obj X) 0 0), pb l y 0 (q ⊗ₜ x) = q ⊗ₜ pullHl l (sch.map y) 0 0 x`.

Introduce `X y q x`. Simplify using `only [pb, pullHQ, LinearMap.baseChange_tmul]`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `X n hn`. Conclude with `sub_of l (fun j => ((In.a9 hI) (ZMod (l ^ j)) (tw (l ^ j) 0)).1 (sch.obj X) n hn)`.

Introduce `n hn`. Conclude with `sub_of l (fun j => hP hI k (l ^ j) n 0 hn)`. Introduce `z`. Take `⟨b, x, hb, rfl⟩` from `tensor_form l z`. Take `⟨c, rfl⟩` from `hsurj x`.

Use `⟨(c : ℚ_[l]) * (b : ℚ_[l])⁻¹, ?_, ?_⟩` and prove the remaining obligations. Apply `Φ.injective` to reduce the goal to its premises. Rewrite using `[hΦr, hΦ, he]`. Introduce `r hr`. Establish `h1` using `congrArg Φ hr`.

Rewrite `h1` using `[hΦr, hΦ, he]`. Conclude with `h1.symm`. Introduce `X p hp z hz`. Take `⟨b, x, hb, rfl⟩` from `tensor_form l z`. Establish `hx : x = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Apply `((hT j).2 p hp (x.1 j)).1` to reduce the goal to its premises. Introduce `y`. Establish `h1` using `hz y`.

Rewrite `h1` using `[hpb]`. Establish `h2` using `key b _ hb h1`. Conclude with `congrArg (fun w : Hl l (sch.obj (S k)) 0 0 => w.1 j) h2`. Rewrite using `[hx, TensorProduct.tmul_zero]`. Introduce `X p hp hc z y y'`.

Take `⟨b, x, hb, rfl⟩` from `tensor_form l z`. Rewrite using `[hpb, hpb]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `j`.

Conclude with `((hT j).2 p hp (x.1 j)).2 hc y y'`.
-/
theorem lowL_holds : LowL := by
  intro hI hP l _ k _ _ hl hR hT
  have hu : IsUnit ((l : ℕ) : Γ(S k, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.mpr hl).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  obtain ⟨ω, hω, hone⟩ := hR.one_def (S k) hu
  obtain ⟨hsurj, hinj⟩ := rep_of ω
    (fun j z => by
      obtain ⟨a, ha⟩ := (hT j).1.1 z
      exact ⟨a, by rw [ha]; simp [lv, hω]⟩)
    (fun j a ha => (hT j).1.2 a (by simpa [lv, hω] using ha))
  let e : ℤ_[l] ≃ₗ[ℤ_[l]] Hl l (sch.obj (S k)) 0 0 :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[l] _ ω)
      ⟨fun c d hcd => by
        have h0 : (c - d) • ω = 0 := by
          simpa [sub_smul, sub_eq_zero] using hcd
        exact sub_eq_zero.mp (hinj _ h0),
       fun x => by
        obtain ⟨c, hc⟩ := hsurj x
        exact ⟨c, by simp [hc]⟩⟩
  let Φ : V l (S k) 0 ≃ₗ[ℤ_[l]] ℚ_[l] :=
    (TensorProduct.congr (LinearEquiv.refl ℤ_[l] ℚ_[l]) e.symm).trans (TensorProduct.rid ℤ_[l] ℚ_[l])
  have hΦ : ∀ (q : ℚ_[l]) (u : Hl l (sch.obj (S k)) 0 0),
      Φ (q ⊗ₜ u) = ((e.symm u : ℤ_[l]) : ℚ_[l]) * q := by
    intro q u
    simp [Φ, Algebra.smul_def]
  have he : ∀ c : ℤ_[l], e.symm (c • ω) = c := by
    intro c
    rw [LinearEquiv.symm_apply_eq]
    rfl
  have hsm : ∀ r : ℚ_[l], r • oneV l (S k) = r ⊗ₜ ω := by
    intro r
    rw [hone, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hΦr : ∀ r : ℚ_[l], Φ (r • oneV l (S k)) = r := by
    intro r
    rw [hsm, hΦ]
    have := he 1
    rw [one_smul] at this
    rw [this]
    simp
  have key : ∀ (b : ℤ_[l]) (u : Hl l (sch.obj (S k)) 0 0), b ≠ 0 →
      ((b : ℚ_[l])⁻¹ ⊗ₜ[ℤ_[l]] u : V l (S k) 0) = 0 → u = 0 := by
    intro b u hb h
    have h1 := congrArg Φ h
    rw [hΦ, map_zero] at h1
    have hb' : (b : ℚ_[l]) ≠ 0 := fun h' => hb (Subtype.ext h')
    have h2 : ((e.symm u : ℤ_[l]) : ℚ_[l]) = 0 := by
      rcases mul_eq_zero.mp h1 with h3 | h3
      · exact h3
      · exact absurd h3 (inv_ne_zero hb')
    have h4 : e.symm u = 0 := Subtype.ext h2
    simpa using congrArg e h4
  have hpb : ∀ {X : Scheme} (y : S k ⟶ X) (q : ℚ_[l]) (x : Hl l (sch.obj X) 0 0),
      pb l y 0 (q ⊗ₜ x) = q ⊗ₜ pullHl l (sch.map y) 0 0 x := by
    intro X y q x
    simp only [pb, pullHQ, LinearMap.baseChange_tmul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X n hn
    exact sub_of l (fun j => ((In.a9 hI) (ZMod (l ^ j)) (tw (l ^ j) 0)).1 (sch.obj X) n hn)
  · intro n hn
    exact sub_of l (fun j => hP hI k (l ^ j) n 0 hn)
  · intro z
    obtain ⟨b, x, hb, rfl⟩ := tensor_form l z
    obtain ⟨c, rfl⟩ := hsurj x
    refine ⟨(c : ℚ_[l]) * (b : ℚ_[l])⁻¹, ?_, ?_⟩
    · apply Φ.injective
      rw [hΦr, hΦ, he]
    · intro r hr
      have h1 := congrArg Φ hr
      rw [hΦr, hΦ, he] at h1
      exact h1.symm
  · intro X p hp z hz
    obtain ⟨b, x, hb, rfl⟩ := tensor_form l z
    have hx : x = 0 := by
      apply Subtype.ext
      funext j
      apply ((hT j).2 p hp (x.1 j)).1
      intro y
      have h1 := hz y
      rw [hpb] at h1
      have h2 := key b _ hb h1
      exact congrArg (fun w : Hl l (sch.obj (S k)) 0 0 => w.1 j) h2
    rw [hx, TensorProduct.tmul_zero]
  · intro X p hp hc z y y'
    obtain ⟨b, x, hb, rfl⟩ := tensor_form l z
    rw [hpb, hpb]
    congr 1
    apply Subtype.ext
    funext j
    exact ((hT j).2 p hp (x.1 j)).2 hc y y'

end UpperTheory.Gal.KunnethLefschetz
