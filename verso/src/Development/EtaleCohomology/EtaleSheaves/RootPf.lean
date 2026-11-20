import Development.EtaleCohomology.EtaleSheaves.ChartSurjCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.RootPf

/- English proof (translation)
Set `f : CommRingCat.of A ⟶ Γ(Z, U)` to `(Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ Z.presheaf.map (homOfLE le_top).op`. Use `hq.map f.hom` as an intermediate fact. Simplify using `using this`.
-/
lemma unit_sec {Z : Scheme.{0}} (q : ℕ) (A : Type) [CommRing A] (p : Z ⟶ Spec (CommRingCat.of A))
    (hq : IsUnit (q : A)) (U : Z.Opens) : IsUnit (q : Γ(Z, U)) := by
  let f : CommRingCat.of A ⟶ Γ(Z, U) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ Z.presheaf.map (homOfLE le_top).op
  have := hq.map f.hom
  simpa using this

/- English proof (translation)
Establish `: NeZero (q : T)` using `⟨hq.ne_zero⟩`. Take `⟨a, ha⟩` from `hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T) (by rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q)))`. Conclude with `⟨a, (Polynomial.isRoot_cyclotomic_iff (n := q) (μ := a)).1 ha⟩`.
-/
lemma prim_of_aic (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] (hT : AIC T)
    (hq : IsUnit (q : T)) : ∃ a : T, IsPrimitiveRoot a q := by
  have : NeZero (q : T) := ⟨hq.ne_zero⟩
  obtain ⟨a, ha⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T)
    (by rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q)))
  exact ⟨a, (Polynomial.isRoot_cyclotomic_iff (n := q) (μ := a)).1 ha⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `prim_of_aic q Γ(Z, V) (hZ V hV (by obtain ⟨x⟩ := hne; exact ⟨x.1, x.2⟩)) (hqU V)`. Establish `hb` using `ha.map_of_injective (f := (Z.germToFunctionField V).hom) (Z.germToFunctionField_injective V)`. Take `⟨i, -, hi⟩` from `hb.eq_pow_of_pow_eq_one hζ.pow_eq_one`. Conclude with `⟨a ^ i, by rw [map_pow]; exact hi⟩`.
-/
lemma local_root {Z : Scheme.{0}} [IsIntegral Z]
    (hZ : ∀ U : Z.Opens, IsAffineOpen U → (U : Set Z).Nonempty → AIC Γ(Z, U))
    (q : ℕ) [NeZero q] (hqU : ∀ U : Z.Opens, IsUnit (q : Γ(Z, U))) (ζ : Z.functionField)
    (hζ : IsPrimitiveRoot ζ q) (V : Z.Opens) (hV : IsAffineOpen V) [hne : Nonempty V] :
    ∃ s : Γ(Z, V), (Z.germToFunctionField V).hom s = ζ := by
  obtain ⟨a, ha⟩ := prim_of_aic q Γ(Z, V)
    (hZ V hV (by obtain ⟨x⟩ := hne; exact ⟨x.1, x.2⟩)) (hqU V)
  have hb := ha.map_of_injective (f := (Z.germToFunctionField V).hom) (Z.germToFunctionField_injective V)
  obtain ⟨i, -, hi⟩ := hb.eq_pow_of_pow_eq_one hζ.pow_eq_one
  exact ⟨a ^ i, by rw [map_pow]; exact hi⟩

/- English proof (translation)
Introduce `q A _ Z p hZ hq`. Take `⟨hI, hA⟩` from `hZ`. Establish `hqU : ∀ U : Z.Opens, IsUnit (q : Γ(Z, U))` using `fun U => unit_sec q A p hq U`. Take `⟨x⟩` from `(inferInstance : Nonempty Z)`. Establish `: Nonempty (⊤ : Z.Opens)` using `⟨⟨x, trivial⟩⟩`.

Establish `hq0 : NeZero q` using `⟨by rintro rfl; exact not_isUnit_zero (M₀ := Γ(Z, ⊤)) (by simpa using hqU ⊤)⟩`. Establish `hbasis : ∀ {U : Z.Opens} {y : Z}, y ∈ U → ∃ U' ∈ Z.affineOpens, y ∈ U' ∧ U' ≤ U` using `TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens`. Establish `haff : ∀ y : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ y ∈ U`. Introduce `y`. Take `⟨U, hU, hy, -⟩` from `hbasis (show y ∈ (⊤ : Z.Opens) from trivial)`.

Conclude with `⟨U, hU, hy⟩`. Take `⟨U₀, hU₀, hx⟩` from `haff x`. Establish `: Nonempty U₀` using `⟨⟨x, hx⟩⟩`. Take `⟨a₀, ha₀⟩` from `prim_of_aic q Γ(Z, U₀) (hA U₀ hU₀ ⟨x, hx⟩) (hqU U₀)`. Use `set ζ : Z.functionField := (Z.germToFunctionField U₀).hom a₀ with hζdef`.

Establish `hζ : IsPrimitiveRoot ζ q` using `ha₀.map_of_injective (f := (Z.germToFunctionField U₀).hom) (Z.germToFunctionField_injective U₀)`. Set `ι` to `{V : Z.Opens // IsAffineOpen V ∧ Nonempty V}`. Set `U : ι → Z.Opens` to `fun i => i.1`. Establish `instU : ∀ i : ι, Nonempty (U i)` using `fun i => i.2.2`. Establish `hex : ∀ i : ι, ∃ s : Γ(Z, U i), (Z.germToFunctionField (U i)).hom s = ζ` using `fun i => @local_root Z hI hA q hq0 hqU ζ hζ i.1 i.2.1 i.2.2`.

Set `sf : ∀ i : ι, Γ(Z, U i)` to `fun i => Classical.choose (hex i)`. Establish `hsf : ∀ i : ι, (Z.germToFunctionField (U i)).hom (sf i) = ζ` using `fun i => Classical.choose_spec (hex i)`. Establish `hcov : (⊤ : Z.Opens) ≤ iSup U`. Introduce `y _`. Take `⟨V, hV, hy⟩` from `haff y`.

Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, ⟨⟨y, hy⟩⟩⟩, hy⟩`. Establish `hcomp : TopCat.Presheaf.IsCompatible Z.sheaf.1 U sf`. Introduce `i j`. Establish `: Nonempty (U i ⊓ U j : Z.Opens)`. Take `⟨y, hy⟩` from `nonempty_preirreducible_inter (U i).isOpen (U j).isOpen (by obtain ⟨⟨y, hy⟩⟩ := i.2.2; exact ⟨y, hy⟩) (by obtain ⟨⟨y, hy⟩⟩ := j.2.2; exact ⟨y, hy⟩)`.

Conclude with `⟨⟨y, hy⟩⟩`. Apply `Z.germToFunctionField_injective (U i ⊓ U j)` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Z.presheaf.germ _ _ _ (Z.presheaf.map _ (sf i)) = Z.presheaf.germ _ _ _ (Z.presheaf.map _ (sf j))`. Rewrite using `[TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]`. Conclude with `(hsf i).trans (hsf j).symm`.

Take `⟨s0, hs, -⟩` from `Z.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hcov sf hcomp`. Set `s : Γ(Z, ⊤)` to `s0`. Express the relevant statement in the definitionally equal form `∀ i : ι, Z.presheaf.map (homOfLE le_top).op s = sf i at hs`. Establish `hgs : (Z.germToFunctionField ⊤).hom s = ζ`. Establish `h1` using `hs ⟨U₀, hU₀, inferInstance⟩`.

Establish `h2` using `hsf ⟨U₀, hU₀, inferInstance⟩`. Rewrite `h2` using `[← h1]`. Express the relevant statement in the definitionally equal form `Z.presheaf.germ _ _ _ (Z.presheaf.map _ s) = ζ at h2`. Rewrite `h2` using `[TopCat.Presheaf.germ_res_apply]`. Conclude with `h2`.

Establish `hps : IsPrimitiveRoot s q`. Establish `h' : IsPrimitiveRoot ((Z.germToFunctionField ⊤).hom s) q` using `by rw [hgs]; exact hζ`. Conclude with `IsPrimitiveRoot.of_map_of_injective h' (Z.germToFunctionField_injective ⊤)`. Establish `: NeZero (q : Γ(Z, ⊤))` using `⟨(hqU ⊤).ne_zero⟩`. Use `⟨⟨s, hqU ⊤, ?_⟩⟩` and prove the remaining obligations.

Establish `hr` using `(Polynomial.isRoot_cyclotomic_iff (n := q) (μ := s)).2 hps`. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]`. Conclude with `hr`.
-/
theorem Root_of : LateralTheory.E.ChartSurjCut.Root := by
  intro q A _ Z p hZ hq
  obtain ⟨hI, hA⟩ := hZ
  have hqU : ∀ U : Z.Opens, IsUnit (q : Γ(Z, U)) := fun U => unit_sec q A p hq U
  obtain ⟨x⟩ := (inferInstance : Nonempty Z)
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨x, trivial⟩⟩
  have hq0 : NeZero q := ⟨by rintro rfl; exact not_isUnit_zero (M₀ := Γ(Z, ⊤)) (by simpa using hqU ⊤)⟩
  have hbasis : ∀ {U : Z.Opens} {y : Z}, y ∈ U → ∃ U' ∈ Z.affineOpens, y ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
  have haff : ∀ y : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ y ∈ U := by
    intro y
    obtain ⟨U, hU, hy, -⟩ := hbasis (show y ∈ (⊤ : Z.Opens) from trivial)
    exact ⟨U, hU, hy⟩
  obtain ⟨U₀, hU₀, hx⟩ := haff x
  have : Nonempty U₀ := ⟨⟨x, hx⟩⟩
  obtain ⟨a₀, ha₀⟩ := prim_of_aic q Γ(Z, U₀) (hA U₀ hU₀ ⟨x, hx⟩) (hqU U₀)
  set ζ : Z.functionField := (Z.germToFunctionField U₀).hom a₀ with hζdef
  have hζ : IsPrimitiveRoot ζ q :=
    ha₀.map_of_injective (f := (Z.germToFunctionField U₀).hom) (Z.germToFunctionField_injective U₀)
  let ι := {V : Z.Opens // IsAffineOpen V ∧ Nonempty V}
  let U : ι → Z.Opens := fun i => i.1
  have instU : ∀ i : ι, Nonempty (U i) := fun i => i.2.2
  have hex : ∀ i : ι, ∃ s : Γ(Z, U i), (Z.germToFunctionField (U i)).hom s = ζ := fun i =>
    @local_root Z hI hA q hq0 hqU ζ hζ i.1 i.2.1 i.2.2
  let sf : ∀ i : ι, Γ(Z, U i) := fun i => Classical.choose (hex i)
  have hsf : ∀ i : ι, (Z.germToFunctionField (U i)).hom (sf i) = ζ := fun i => Classical.choose_spec (hex i)
  have hcov : (⊤ : Z.Opens) ≤ iSup U := by
    intro y _
    obtain ⟨V, hV, hy⟩ := haff y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, ⟨⟨y, hy⟩⟩⟩, hy⟩
  have hcomp : TopCat.Presheaf.IsCompatible Z.sheaf.1 U sf := by
    intro i j
    have : Nonempty (U i ⊓ U j : Z.Opens) := by
      obtain ⟨y, hy⟩ := nonempty_preirreducible_inter (U i).isOpen (U j).isOpen
        (by obtain ⟨⟨y, hy⟩⟩ := i.2.2; exact ⟨y, hy⟩) (by obtain ⟨⟨y, hy⟩⟩ := j.2.2; exact ⟨y, hy⟩)
      exact ⟨⟨y, hy⟩⟩
    apply Z.germToFunctionField_injective (U i ⊓ U j)
    change Z.presheaf.germ _ _ _ (Z.presheaf.map _ (sf i)) = Z.presheaf.germ _ _ _ (Z.presheaf.map _ (sf j))
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact (hsf i).trans (hsf j).symm
  obtain ⟨s0, hs, -⟩ := Z.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hcov sf hcomp
  let s : Γ(Z, ⊤) := s0
  change ∀ i : ι, Z.presheaf.map (homOfLE le_top).op s = sf i at hs
  have hgs : (Z.germToFunctionField ⊤).hom s = ζ := by
    have h1 := hs ⟨U₀, hU₀, inferInstance⟩
    have h2 := hsf ⟨U₀, hU₀, inferInstance⟩
    rw [← h1] at h2
    change Z.presheaf.germ _ _ _ (Z.presheaf.map _ s) = ζ at h2
    rw [TopCat.Presheaf.germ_res_apply] at h2
    exact h2
  have hps : IsPrimitiveRoot s q := by
    have h' : IsPrimitiveRoot ((Z.germToFunctionField ⊤).hom s) q := by rw [hgs]; exact hζ
    exact IsPrimitiveRoot.of_map_of_injective h' (Z.germToFunctionField_injective ⊤)
  have : NeZero (q : Γ(Z, ⊤)) := ⟨(hqU ⊤).ne_zero⟩
  refine ⟨⟨s, hqU ⊤, ?_⟩⟩
  have hr := (Polynomial.isRoot_cyclotomic_iff (n := q) (μ := s)).2 hps
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hr

end LateralTheory.E.RootPf
