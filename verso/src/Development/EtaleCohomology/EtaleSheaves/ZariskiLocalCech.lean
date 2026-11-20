import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.ZariskiLocalCech

def CechSigma : Prop := t_E3Cut.Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens)
  {ι : Type} (V : ι → X.Opens), (∀ j, V j ≤ O) → O ≤ ⨆ j, V j →
  (∀ n : ℕ, Eqv R (sch.map (Limits.Sigma.map fun j : Fin (n + 1) → ι => g ∣_ (⨅ k, V (j k)))) F) →
  Eqv R (sch.map (g ∣_ O)) F

section
variable {R : Type} [CommRing R] {F : Shv R}

/- English proof (translation)
Introduce `n` and use `by have h : ⇑(pull R (f ≫ g) F n) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x rw [h]; exact (hf n).comp (hg n)`.
-/
theorem eqv_comp {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hg : Eqv R g F) :
    Eqv R (f ≫ g) F := fun n => by
  have h : ⇑(pull R (f ≫ g) F n) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [h]; exact (hf n).comp (hg n)

/- English proof (translation)
Introduce `n` and use `by have h1 : ∀ x, pull R (inv f) F n (pull R f F n x) = x := fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id] have h2 : ∀ x, pull R f F n (pull R (inv f) F n x) = x := fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id] exact ⟨Function.LeftInverse.injective h1, Functio …`.
-/
theorem eqv_iso {E E' : Spc} (f : E ⟶ E') [IsIso f] : Eqv R f F := fun n => by
  have h1 : ∀ x, pull R (inv f) F n (pull R f F n x) = x := fun x => by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R f F n (pull R (inv f) F n x) = x := fun x => by
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

/- English proof (translation)
Introduce `n` and use `by have key : (fun (x : H R (sch.obj (∐ X)) F n) (j : ι) => pull R (sch.map (Sigma.ι Y j)) F n (pull R (sch.map (Limits.Sigma.map f)) F n x)) = Pi.map (fun j => pull R (sch.map (f j)) F n) ∘ (fun (x : H R (sch.obj (∐ X)) F n) (j : ι) => pull R (sch.map (Sigma.ι X j)) F n x) := by …`.
-/
theorem sigmaEqv (hC : t_E3Cut.Coprod) {ι : Type} {Y X : ι → Scheme.{0}} (f : ∀ j, Y j ⟶ X j)
    (hf : ∀ j, Eqv R (sch.map (f j)) F) : Eqv R (sch.map (Limits.Sigma.map f)) F := fun n => by
  have key : (fun (x : H R (sch.obj (∐ X)) F n) (j : ι) => pull R (sch.map (Sigma.ι Y j)) F n
      (pull R (sch.map (Limits.Sigma.map f)) F n x)) =
      Pi.map (fun j => pull R (sch.map (f j)) F n) ∘
        (fun (x : H R (sch.obj (∐ X)) F n) (j : ι) => pull R (sch.map (Sigma.ι X j)) F n x) := by
    funext x j
    simp only [Function.comp_apply, Pi.map_apply]
    rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, Sigma.ι_map]
  have hb := (Function.Bijective.piMap (fun j => hf j n)).comp (hC R F X n)
  rw [← key] at hb
  exact (Function.Bijective.of_comp_iff' (hC R F Y n) _).1 hb

/- English proof (translation)
Establish `: IsIso (⊤ : X.Opens).ι` using `isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)`. Establish `: IsIso (g ⁻¹ᵁ ⊤).ι` using `isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)`. Establish `e : g = inv (g ⁻¹ᵁ ⊤).ι ≫ (g ∣_ ⊤) ≫ (⊤ : X.Opens).ι`. Rewrite using `[morphismRestrict_ι, IsIso.inv_hom_id_assoc]`. Rewrite using `[e, Functor.map_comp, Functor.map_comp]`.

Conclude with `eqv_comp (eqv_iso _) (eqv_comp h (eqv_iso _))`.
-/
theorem eqv_of_top {Y X : Scheme.{0}} (g : Y ⟶ X) (h : Eqv R (sch.map (g ∣_ ⊤)) F) : Eqv R (sch.map g) F := by
  have : IsIso (⊤ : X.Opens).ι := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  have : IsIso (g ⁻¹ᵁ ⊤).ι := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  have e : g = inv (g ⁻¹ᵁ ⊤).ι ≫ (g ∣_ ⊤) ≫ (⊤ : X.Opens).ι := by
    rw [morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  rw [e, Functor.map_comp, Functor.map_comp]
  exact eqv_comp (eqv_iso _) (eqv_comp h (eqv_iso _))

end

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [X.basicOpen_of_isUnit isUnit_one]`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.inf_insert, Finset.prod_insert ha, Scheme.basicOpen_mul, ← ih, inf_assoc]`.
-/
theorem inf_basicOpen {X : Scheme.{0}} {A : X.Opens} {κ : Type} [DecidableEq κ] (f : κ → Γ(X, A)) (s : Finset κ) :
    (s.inf fun k => X.basicOpen (f k)) ⊓ A = X.basicOpen (∏ k ∈ s, f k) := by
  induction s using Finset.induction_on with
  | empty => simp [X.basicOpen_of_isUnit isUnit_one]
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.prod_insert ha, Scheme.basicOpen_mul, ← ih, inf_assoc]

/- English proof (translation)
Rewrite using `[← inf_basicOpen f Finset.univ, Finset.inf_univ_eq_iInf]`. Conclude with `(inf_eq_left.2 ((iInf_le (fun k => X.basicOpen (f k)) 0).trans (X.basicOpen_le (f 0)))).symm`.
-/
theorem iInf_basicOpen {X : Scheme.{0}} {A : X.Opens} {n : ℕ} (f : Fin (n + 1) → Γ(X, A)) :
    (⨅ k, X.basicOpen (f k)) = X.basicOpen (∏ k, f k) := by
  rw [← inf_basicOpen f Finset.univ, Finset.inf_univ_eq_iInf]
  exact (inf_eq_left.2 ((iInf_le (fun k => X.basicOpen (f k)) 0).trans (X.basicOpen_le (f 0)))).symm

/- English proof (translation)
Introduce `hH R _ F Y X g hU`. Use `choose U hxU hUe using hU`. Establish `hA : ∀ x : X, ∃ A : X.Opens, IsAffineOpen A ∧ x ∈ A ∧ A ≤ U x` using `fun x => by`. Take `⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (hxU x) (U x).2`. Conclude with `⟨V, hV, hxV, hVU⟩`.

Use `choose A hAaff hxA hAU using hA`. Establish `st1 : ∀ (x : X) (O : X.Opens), O ≤ A x → Eqv R (sch.map (g ∣_ O)) F`. Introduce `x O hO`. Use `hCS hH R F g O (ι := {f : Γ(X, A x) // X.basicOpen f ≤ O}) (fun f => X.basicOpen f.1) (fun f => f.2) ?_ ?_` and prove the remaining obligations. Introduce `y hy`.

Take `⟨f, hfO, hyf⟩` from `(hAaff x).exists_basicOpen_le ⟨y, hy⟩ (hO hy)`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hfO⟩, hyf⟩`. Introduce `n`. Apply `sigmaEqv hCop` to reduce the goal to its premises. Introduce `j`.

Establish `e` using `iInf_basicOpen (X := X) (A := A x) (fun k => (j k).1)`. Apply `hUe x` to reduce the goal to its premises. Rewrite using `[e]`. Conclude with `(hAaff x).basicOpen _`. Conclude with `(iInf_le _ 0).trans ((X.basicOpen_le _).trans (hAU x))`.

Use `eqv_of_top g (hCS hH R F g ⊤ A (fun _ => le_top) ?_ ?_)` and prove the remaining obligations. Introduce `y _`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨y, hxA y⟩`. Conclude with `fun n => sigmaEqv hCop _ fun j => st1 (j 0) _ (iInf_le _ 0)`.
-/
theorem ZarLocal_of (hCop : t_E3Cut.Coprod) (hCS : CechSigma) : t_E3Cut.ZarLocal := by
  intro hH R _ F Y X g hU
  choose U hxU hUe using hU
  have hA : ∀ x : X, ∃ A : X.Opens, IsAffineOpen A ∧ x ∈ A ∧ A ≤ U x := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (hxU x) (U x).2
    exact ⟨V, hV, hxV, hVU⟩
  choose A hAaff hxA hAU using hA
  have st1 : ∀ (x : X) (O : X.Opens), O ≤ A x → Eqv R (sch.map (g ∣_ O)) F := by
    intro x O hO
    refine hCS hH R F g O (ι := {f : Γ(X, A x) // X.basicOpen f ≤ O}) (fun f => X.basicOpen f.1) (fun f => f.2) ?_ ?_
    · intro y hy
      obtain ⟨f, hfO, hyf⟩ := (hAaff x).exists_basicOpen_le ⟨y, hy⟩ (hO hy)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hfO⟩, hyf⟩
    · intro n
      apply sigmaEqv hCop
      intro j
      have e := iInf_basicOpen (X := X) (A := A x) (fun k => (j k).1)
      apply hUe x
      · rw [e]; exact (hAaff x).basicOpen _
      · exact (iInf_le _ 0).trans ((X.basicOpen_le _).trans (hAU x))
  refine eqv_of_top g (hCS hH R F g ⊤ A (fun _ => le_top) ?_ ?_)
  · intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hxA y⟩
  · exact fun n => sigmaEqv hCop _ fun j => st1 (j 0) _ (iInf_le _ 0)

end LateralTheory.E.ZariskiLocalCech
