import Development.EtaleCohomology.EtaleSheaves.SteinPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Polynomial

namespace LateralTheory.E.AICOpenPf
open LateralTheory.E.t_E2Cut LateralTheory.E.SteinPf

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `p hd hm β hβ`. Establish `: p = 1` using `hm.natDegree_eq_zero.mp hd`.

Substitute `this` using the available equality. Simplify using `at hβ`. Consider the case `succ n ih`. Introduce `p hd hm β hβ`. Take `⟨a, ha⟩` from `hA p hm (by omega)`.

Establish `hfac : (X - C a) * (p /ₘ (X - C a)) = p` using `mul_divByMonic_eq_iff_isRoot.mpr ha`. Establish `hqm : (p /ₘ (X - C a)).Monic` using `(monic_X_sub_C a).of_mul_monic_left (by rw [hfac]; exact hm)`. Establish `hqd : (p /ₘ (X - C a)).natDegree = n`. Rewrite using `[natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers.

Rewrite `hβ` using `[← hfac, Polynomial.map_mul, eval_mul, mul_eq_zero]`. Break down `hβ with h | h` into its components or cases. Use `⟨a, ?_⟩` and prove the remaining obligations. Simplify using `at h`. Rewrite `h` using `[sub_eq_zero]`.

Conclude with `h.symm`. Conclude with `ih _ hqd hqm β h`.
-/
theorem roots_in {A K : Type} [CommRing A] [IsDomain A] [CommRing K] [IsDomain K] (φ : A →+* K) (hA : AIC A) :
    ∀ n (p : A[X]), p.natDegree = n → p.Monic → ∀ β : K, (p.map φ).eval β = 0 → ∃ a, φ a = β := by
  intro n
  induction n with
  | zero =>
    intro p hd hm β hβ
    have : p = 1 := hm.natDegree_eq_zero.mp hd
    subst this; simp at hβ
  | succ n ih =>
    intro p hd hm β hβ
    obtain ⟨a, ha⟩ := hA p hm (by omega)
    have hfac : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hqm : (p /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [hfac]; exact hm)
    have hqd : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    rw [← hfac, Polynomial.map_mul, eval_mul, mul_eq_zero] at hβ
    rcases hβ with h | h
    · refine ⟨a, ?_⟩
      simp at h; rw [sub_eq_zero] at h; exact h.symm
    · exact ih _ hqd hqm β h

/- English proof (translation)
Simplify using `only [Scheme.germToFunctionField]`. Rewrite using `[← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_res]`.
-/
theorem gtf_res {Z : Scheme.{0}} [IsIntegral Z] {U W : Z.Opens} (i : U ⟶ W) [Nonempty U] [Nonempty W] (s : Γ(Z, W)) :
    Z.germToFunctionField U (Z.presheaf.map i.op s) = Z.germToFunctionField W s := by
  simp only [Scheme.germToFunctionField]
  rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_res]

/- English proof (translation)
Use extensionality with `s`. Conclude with `gtf_res i s`.
-/
theorem gtf_res_hom {Z : Scheme.{0}} [IsIntegral Z] {U W : Z.Opens} (i : U ⟶ W) [Nonempty U] [Nonempty W] :
    (Z.germToFunctionField U).hom.comp (Z.presheaf.map i.op).hom = (Z.germToFunctionField W).hom := by
  ext s; exact gtf_res i s

/- English proof (translation)
Introduce `Z hZ W hW p hm hd`. Establish `: IsIntegral Z` using `hZ.1`. Establish `: Nonempty W` using `⟨⟨_, hW.some_mem⟩⟩`. Establish `hcov : ∀ x : W, ∃ U : Z.Opens, IsAffineOpen U ∧ (x : Z) ∈ U ∧ U ≤ W`. Introduce `x`.

Take `⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩` from `Z.isBasis_affineOpens.exists_subset_of_mem_open x.2 W.isOpen`. Conclude with `⟨U, hU, hxU, hUW⟩`. Use `choose U hUa hxU hUW using hcov`. Establish `hne : ∀ x : W, Nonempty (U x)` using `fun x => ⟨⟨_, hxU x⟩⟩`. Set `ψ` to `Z.germToFunctionField W`.

Establish `hroot : ∀ x : W, ∃ β : Z.functionField, (p.map ψ.hom).eval β = 0`. Introduce `x`. Use `hne x` as an intermediate fact. Establish `hA : AIC Γ(Z, U x)` using `hZ.2 _ (hUa x) ⟨_, hxU x⟩`. Set `ρ` to `(Z.presheaf.map (homOfLE (hUW x)).op).hom`.

Take `⟨r, hr⟩` from `hA (p.map ρ) (hm.map ρ) (by rw [hm.natDegree_map]; exact hd)`. Use `⟨Z.germToFunctionField (U x) r, ?_⟩` and prove the remaining obligations. Rewrite using `[← gtf_res_hom (homOfLE (hUW x)), ← Polynomial.map_map, Polynomial.eval_map_apply, hr, map_zero]`. Take `⟨β, hβ⟩` from `hroot ⟨_, hW.some_mem⟩`. Establish `hsec : ∀ x : W, ∃ t : Γ(Z, U x), Z.germToFunctionField (U x) t = β`.

Introduce `x`. Use `hne x` as an intermediate fact. Establish `hA : AIC Γ(Z, U x)` using `hZ.2 _ (hUa x) ⟨_, hxU x⟩`. Set `ρ` to `(Z.presheaf.map (homOfLE (hUW x)).op).hom`. Conclude with `roots_in (Z.germToFunctionField (U x)).hom hA _ (p.map ρ) rfl (hm.map ρ) β (by rw [Polynomial.map_map, gtf_res_hom]; exact hβ)`.

Use `choose sf hsf using hsec`. Establish `hcompat : TopCat.Presheaf.IsCompatible Z.sheaf.1 U sf`. Introduce `i j`. Use `hne i` as an intermediate fact. Use `hne j` as an intermediate fact.

Establish `hij : ((U i ⊓ U j : Z.Opens) : Set Z).Nonempty` using `nonempty_preirreducible_inter (U i).isOpen (U j).isOpen ⟨_, hxU i⟩ ⟨_, hxU j⟩`. Establish `: Nonempty (U i ⊓ U j : Z.Opens)` using `⟨⟨_, hij.some_mem⟩⟩`. Apply `Z.germToFunctionField_injective (U i ⊓ U j)` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Z.germToFunctionField _ (Z.presheaf.map _ (sf i)) = Z.germToFunctionField _ (Z.presheaf.map _ (sf j))`. Rewrite using `[gtf_res, gtf_res, hsf, hsf]`.

Take `⟨s, hs, -⟩` from `Z.sheaf.existsUnique_gluing' (U := U) (V := W) (iUV := fun x => homOfLE (hUW x)) (hcover := fun y hy => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxU _⟩) (sf := sf) (h := hcompat)`. Establish `hsβ : ψ s = β`. Establish `h0` using `hs ⟨_, hW.some_mem⟩`. Use `hne ⟨_, hW.some_mem⟩` as an intermediate fact. Rewrite using `[← hsf ⟨_, hW.some_mem⟩, ← gtf_res (homOfLE (hUW ⟨_, hW.some_mem⟩)) s]`.

Conclude with `congrArg _ h0`. Take `⟨t, ht⟩ : ∃ t : Γ(Z, W), ψ t = β` from `⟨s, hsβ⟩`. Use `⟨t, Z.germToFunctionField_injective W ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero]`. Establish `key : ψ.hom (p.eval t) = (p.map ψ.hom).eval (ψ.hom t)`.

Rewrite using `[Polynomial.eval_map, Polynomial.eval₂_hom]`. Express the relevant statement in the definitionally equal form `ψ.hom (p.eval t) = 0`. Rewrite using `[key]`. Express the relevant statement in the definitionally equal form `(p.map ψ.hom).eval (ψ t) = 0`. Rewrite using `[ht]`.

Conclude with `hβ`.
-/
theorem AICOpen_of : AICOpen := by
  intro Z hZ W hW p hm hd
  have : IsIntegral Z := hZ.1
  have : Nonempty W := ⟨⟨_, hW.some_mem⟩⟩
  have hcov : ∀ x : W, ∃ U : Z.Opens, IsAffineOpen U ∧ (x : Z) ∈ U ∧ U ≤ W := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open x.2 W.isOpen
    exact ⟨U, hU, hxU, hUW⟩
  choose U hUa hxU hUW using hcov
  have hne : ∀ x : W, Nonempty (U x) := fun x => ⟨⟨_, hxU x⟩⟩
  let ψ := Z.germToFunctionField W

  have hroot : ∀ x : W, ∃ β : Z.functionField, (p.map ψ.hom).eval β = 0 := by
    intro x
    have := hne x
    have hA : AIC Γ(Z, U x) := hZ.2 _ (hUa x) ⟨_, hxU x⟩
    let ρ := (Z.presheaf.map (homOfLE (hUW x)).op).hom
    obtain ⟨r, hr⟩ := hA (p.map ρ) (hm.map ρ) (by rw [hm.natDegree_map]; exact hd)
    refine ⟨Z.germToFunctionField (U x) r, ?_⟩
    rw [← gtf_res_hom (homOfLE (hUW x)), ← Polynomial.map_map, Polynomial.eval_map_apply, hr, map_zero]
  obtain ⟨β, hβ⟩ := hroot ⟨_, hW.some_mem⟩
  have hsec : ∀ x : W, ∃ t : Γ(Z, U x), Z.germToFunctionField (U x) t = β := by
    intro x
    have := hne x
    have hA : AIC Γ(Z, U x) := hZ.2 _ (hUa x) ⟨_, hxU x⟩
    let ρ := (Z.presheaf.map (homOfLE (hUW x)).op).hom
    exact roots_in (Z.germToFunctionField (U x)).hom hA _ (p.map ρ) rfl (hm.map ρ) β
      (by rw [Polynomial.map_map, gtf_res_hom]; exact hβ)
  choose sf hsf using hsec
  have hcompat : TopCat.Presheaf.IsCompatible Z.sheaf.1 U sf := by
    intro i j
    have := hne i; have := hne j
    have hij : ((U i ⊓ U j : Z.Opens) : Set Z).Nonempty :=
      nonempty_preirreducible_inter (U i).isOpen (U j).isOpen ⟨_, hxU i⟩ ⟨_, hxU j⟩
    have : Nonempty (U i ⊓ U j : Z.Opens) := ⟨⟨_, hij.some_mem⟩⟩
    apply Z.germToFunctionField_injective (U i ⊓ U j)
    change Z.germToFunctionField _ (Z.presheaf.map _ (sf i)) = Z.germToFunctionField _ (Z.presheaf.map _ (sf j))
    rw [gtf_res, gtf_res, hsf, hsf]
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (U := U) (V := W) (iUV := fun x => homOfLE (hUW x))
    (hcover := fun y hy => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxU _⟩) (sf := sf) (h := hcompat)
  have hsβ : ψ s = β := by
    have h0 := hs ⟨_, hW.some_mem⟩
    have := hne ⟨_, hW.some_mem⟩
    rw [← hsf ⟨_, hW.some_mem⟩, ← gtf_res (homOfLE (hUW ⟨_, hW.some_mem⟩)) s]
    exact congrArg _ h0
  obtain ⟨t, ht⟩ : ∃ t : Γ(Z, W), ψ t = β := ⟨s, hsβ⟩
  refine ⟨t, Z.germToFunctionField_injective W ?_⟩
  rw [map_zero]
  have key : ψ.hom (p.eval t) = (p.map ψ.hom).eval (ψ.hom t) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  change ψ.hom (p.eval t) = 0
  rw [key]; change (p.map ψ.hom).eval (ψ t) = 0
  rw [ht]; exact hβ

end LateralTheory.E.AICOpenPf
