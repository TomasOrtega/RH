import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

/- English proof (translation)
Take `⟨f, hf, hc, hz⟩` from `hr`. Conclude with `⟨f, hf, hc, fun s => (hz s).trans (Ideal.Quotient.eq.2 (h s))⟩`.
-/
theorem rep_congr {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : CH.H (sq a b) j}
    (h : ∀ s, z s - z' s ∈ b.S _) (hr : Rep a b z c) : Rep a b z' c := by
  obtain ⟨f, hf, hc, hz⟩ := hr
  exact ⟨f, hf, hc, fun s => (hz s).trans (Ideal.Quotient.eq.2 (h s))⟩

section Frame
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ} (E : Frame Φ d)
  (σ : ∀ T : C, E.D ⟶ T) {t : Fin d → Φ.A.obj E.D} (ht : E.Coords t) {u : Fin d → ∀ T : C, Φ.A.obj T}
  (hu : ∀ i T, (Φ.A.map (σ T)).hom (t i) = u i T)

include ht hu

/- English proof (translation)
Establish `e : (Φ.A.map (σ T ≫ φ)).hom (t i) = (Φ.A.map φ).hom ((Φ.A.map (σ T)).hom (t i))`. Rewrite using `[Functor.map_comp]`. Both sides reduce to the same expression. Rewrite using `[Frame.a, ht, hu, e, hu]`.
-/
theorem a_eq (i : Fin d) {T T' : C} (φ : T ⟶ T') : E.a σ i φ = u i T' - (Φ.A.map φ).hom (u i T) := by
  have e : (Φ.A.map (σ T ≫ φ)).hom (t i) = (Φ.A.map φ).hom ((Φ.A.map (σ T)).hom (t i)) := by
    rw [Functor.map_comp]; rfl
  rw [Frame.a, ht, hu, e, hu]

/- English proof (translation)
Unfold `Frame.form wz`. Use `congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[a_eq E σ ht hu]`.
-/
theorem form_eq {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (s : ComposableArrows C j) :
    E.form σ I x s = wz u I s * (Φ.A.map (σ _)).hom x := by
  unfold Frame.form wz
  refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
  rw [a_eq E σ ht hu]

/- English proof (translation)
Establish `hm : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T'` using `fun i T T' φ => by`. Rewrite using `[← a_eq E σ ht hu]`. Conclude with `E.mem _ _ _`. Establish `h1` using `wz_mem hF u hm I s`. Establish `h2 : (Φ.A.map (σ _)).hom x - l ∈ (Fil ((1 : ℕ) : ℤ)).S _`.

Simplify `hl` using `[hF.one]`. Establish `h3` using `hF.mul r 1 _ h1 h2`. Rewrite using `[form_eq E σ ht hu, ← mul_sub]`. Simplify using `using h3`.
-/
theorem form_sub_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {r : ℕ} (I : Fin r → Fin d) (x : Φ.A.obj E.D)
    (s : ComposableArrows C r) (l : Φ.A.obj (s.obj (Fin.last r)))
    (hl : (Φ.A.map (σ _)).hom x - l ∈ Φ.J.S _) :
    E.form σ I x s - wz u I s * l ∈ (Fil ((r : ℤ) + 1)).S _ := by
  have hm : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T' := fun i T T' φ => by
    rw [← a_eq E σ ht hu]
    exact E.mem _ _ _
  have h1 := wz_mem hF u hm I s
  have h2 : (Φ.A.map (σ _)).hom x - l ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    simpa [hF.one] using hl
  have h3 := hF.mul r 1 _ h1 h2
  rw [form_eq E σ ht hu, ← mul_sub]
  simpa using h3

end Frame

/- English proof (translation)
Introduce `hFr hLoc hPoly O _ l s hb X q W d c u hu r hr`. Take `⟨E, σ, θ, hGr, hbot, hco, hσ, hpt⟩` from `hFr l s hb q c u hu`. Take `⟨Q, hQ⟩` from `hPoly (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {W}`. Establish `hF : IsFil (sP (SS q l s W)) (sFil (SS q l s W))` using `GlobalTheory.CompanionTheory.DPFil.isFil_sFil (SS q l s W)`. Take `⟨-, hL⟩` from `hLoc Q hF E σ hGr (r : ℤ) (fun r' h => (hQ r' (by omega)).1) r`.

Take `⟨h2, h3⟩` from `hL 0 (by simp)`. Establish `hin : ∀ T : (SS q l s W).FullSubcategory, InU W T.obj` using `fun T => by`. Take `⟨-, V, hV, h⟩` from `T.property`. Rewrite `h` using `[Set.mem_singleton_iff.1 hV]`. Then use the resulting hypothesis. Establish `key : ∀ (y : Idx r d → Γ(X, W)) (z : ComposableArrows (SS q l s W).FullSubcategory r), (∑ I : Idx r d, E.form σ I.1 (θ (y I)) z) - (∑ I : Idx r d, wz (Φ` using `sP (SS q l s W)) (fun i T => u i T.obj) I.1 z * (show (sP (SS q l s W)).A.obj (z.obj (Fin.last r)) from lft W (z.obj (Fin.last r)).obj (y I))) ∈ (sFil (SS q l s W) ((r : ℤ) + 1)).S _ := by`.

Introduce `y z`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Ideal.sum_mem _ fun I _ => ?_` and prove the remaining obligations. Use `form_sub_mem E σ hco (u := fun i T => u i T.obj) (fun i T => hσ i T) hF I.1 _ z _ ?_` and prove the remaining obligations. Establish `h` using `hpt _ (hin (z.obj (Fin.last r))) (y I)`.

Rewrite `h` using `[← lft_spec _ (hin (z.obj (Fin.last r))) (y I)]`. Conclude with `Ideal.Quotient.eq.1 h`. Use `⟨fun cl => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨x, -, hx⟩` from `h2 cl`. Use `⟨fun I => θ.symm (x I), ?_⟩` and prove the remaining obligations.

Use `rep_congr (fun z => ?_) hx` and prove the remaining obligations. Use `key (fun I => θ.symm (x I)) z` as an intermediate fact. Simplify using `using this`. Establish `h4` using `h3 (fun I => θ (x I)) (fun I => by`. Rewrite using `[hF.top _ (by simp)]`.

Use the proof step `trivial) (rep_congr (fun z => by`. Use `Ideal.neg_mem_iff _ |>.2 (key x z)` as an intermediate fact. Simplify using `using this) hx)`. Use function extensionality and compare the values at `I`. Establish `h5` using `h4 I`.

Establish `e : (sFil (SS q l s W) (((0 : ℕ) : ℤ) + 1)).S E.D = ⊥`. Simplify using `using hbot 1 one_ne_zero`. Rewrite `h5` using `[e]`. Conclude with `θ.injective ((Ideal.mem_bot.1 h5).trans (map_zero θ).symm)`.
-/
theorem stLoc : StFrame → KH.LocGr → KH.PolyTf → StLoc := by
  intro hFr hLoc hPoly O _ l s hb X q W d c u hu r hr
  obtain ⟨E, σ, θ, hGr, hbot, hco, hσ, hpt⟩ := hFr l s hb q c u hu
  obtain ⟨Q, hQ⟩ := hPoly (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {W}
  have hF : IsFil (sP (SS q l s W)) (sFil (SS q l s W)) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (SS q l s W)
  obtain ⟨-, hL⟩ := hLoc Q hF E σ hGr (r : ℤ) (fun r' h => (hQ r' (by omega)).1) r
  obtain ⟨h2, h3⟩ := hL 0 (by simp)
  have hin : ∀ T : (SS q l s W).FullSubcategory, InU W T.obj := fun T => by
    obtain ⟨-, V, hV, h⟩ := T.property
    rwa [Set.mem_singleton_iff.1 hV] at h
  have key : ∀ (y : Idx r d → Γ(X, W)) (z : ComposableArrows (SS q l s W).FullSubcategory r),
      (∑ I : Idx r d, E.form σ I.1 (θ (y I)) z) - (∑ I : Idx r d,
        wz (Φ := sP (SS q l s W)) (fun i T => u i T.obj) I.1 z *
          (show (sP (SS q l s W)).A.obj (z.obj (Fin.last r)) from lft W (z.obj (Fin.last r)).obj (y I))) ∈
        (sFil (SS q l s W) ((r : ℤ) + 1)).S _ := by
    intro y z
    rw [← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    refine form_sub_mem E σ hco (u := fun i T => u i T.obj) (fun i T => hσ i T) hF I.1 _ z _ ?_
    have h := hpt _ (hin (z.obj (Fin.last r))) (y I)
    rw [← lft_spec _ (hin (z.obj (Fin.last r))) (y I)] at h
    exact Ideal.Quotient.eq.1 h
  refine ⟨fun cl => ?_, fun x hx => ?_⟩
  · obtain ⟨x, -, hx⟩ := h2 cl
    refine ⟨fun I => θ.symm (x I), ?_⟩
    refine rep_congr (fun z => ?_) hx
    have := key (fun I => θ.symm (x I)) z
    simpa using this
  · have h4 := h3 (fun I => θ (x I)) (fun I => by
      rw [hF.top _ (by simp)]
      trivial) (rep_congr (fun z => by
        have := Ideal.neg_mem_iff _ |>.2 (key x z)
        simpa using this) hx)
    funext I
    have h5 := h4 I
    have e : (sFil (SS q l s W) (((0 : ℕ) : ℤ) + 1)).S E.D = ⊥ := by
      simpa using hbot 1 one_ne_zero
    rw [e] at h5
    exact θ.injective ((Ideal.mem_bot.1 h5).trans (map_zero θ).symm)

end GlobalTheory.CompanionTheory.GrForm
