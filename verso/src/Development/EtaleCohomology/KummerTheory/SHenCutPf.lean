import Development.EtaleCohomology.KummerTheory.SHenCut

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC Polynomial

namespace LateralTheory.KummerTheory.SHenCut

/- English proof (translation)
Introduce `J _ _ D c hc e hF hs x hx`. Take `⟨j, y, rfl⟩` from `Concrete.isColimit_exists_rep D hc x`. Set `ej : D.obj j →+* e.pt` to `(e.ι.app j).hom`. Establish `hy : (hc.desc e).hom ((c.ι.app j).hom y) = ej y` using `congrArg (fun t => t.hom y) (hc.fac e j)`. Establish `hu : IsUnit (ej y)`.

Take `⟨b, hb⟩` from `hF.mul_inv_cancel (a := ej y) (fun h => hx (hy.trans h))`. Conclude with `IsUnit.of_mul_eq_one b hb`. Take `⟨k, f, γ, h1, -⟩` from `hs j (CommRingCat.of (Localization.Away y)) (CommRingCat.ofHom (algebraMap _ _)) (CommRingCat.ofHom (IsLocalization.Away.lift y hu)) (RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway y)) (CommRingCat.hom_ext (IsLocalization.Away.lift_comp y hu))`. Establish `h2 : γ.hom (algebraMap _ (Localization.Away y) y) = (D.map f).hom y` using `congrArg (fun t => t.hom y) h1`. Establish `h3 : (c.ι.app k).hom ((D.map f).hom y) = (c.ι.app j).hom y` using `congrArg (fun t => t.hom y) (c.w f)`.

Establish `h4 : IsUnit ((D.map f).hom y)` using `h2 ▸ (IsLocalization.Away.algebraMap_isUnit y).map γ.hom`. Establish `h5` using `h4.map (c.ι.app k).hom`. Rewrite `h5` using `[h3]`. Conclude with `h5`.
-/
theorem satUnit : SatUnit := by
  intro J _ _ D c hc e hF hs x hx
  obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep D hc x
  let ej : D.obj j →+* e.pt := (e.ι.app j).hom
  have hy : (hc.desc e).hom ((c.ι.app j).hom y) = ej y := congrArg (fun t => t.hom y) (hc.fac e j)
  have hu : IsUnit (ej y) := by
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel (a := ej y) (fun h => hx (hy.trans h))
    exact IsUnit.of_mul_eq_one b hb
  obtain ⟨k, f, γ, h1, -⟩ := hs j (CommRingCat.of (Localization.Away y)) (CommRingCat.ofHom (algebraMap _ _))
    (CommRingCat.ofHom (IsLocalization.Away.lift y hu))
    (RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway y))
    (CommRingCat.hom_ext (IsLocalization.Away.lift_comp y hu))
  have h2 : γ.hom (algebraMap _ (Localization.Away y) y) = (D.map f).hom y := congrArg (fun t => t.hom y) h1
  have h3 : (c.ι.app k).hom ((D.map f).hom y) = (c.ι.app j).hom y := congrArg (fun t => t.hom y) (c.w f)
  have h4 : IsUnit ((D.map f).hom y) := h2 ▸ (IsLocalization.Away.algebraMap_isUnit y).map γ.hom
  have h5 := h4.map (c.ι.app k).hom
  rw [h3] at h5
  exact h5

/- English proof (translation)
Use `choose j y hy using fun n => Concrete.isColimit_exists_rep D hc (f.coeff n)`. Take `⟨S, hS⟩` from `IsFiltered.sup_objs_exists (f.support.image j)`. Use `⟨S, (lifts_iff_coeff_lifts _).2 fun n => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hn : n ∈ f.support`. Take `⟨g⟩` from `hS (Finset.mem_image_of_mem j hn)`.

Conclude with `⟨(D.map g).hom (y n), (congrArg (fun t => t.hom (y n)) (c.w g)).trans (hy n)⟩`. Conclude with `⟨0, (map_zero _).trans (notMem_support_iff.1 hn).symm⟩`.
-/
theorem exists_lift {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c)
    (f : Polynomial c.pt) : ∃ j, f ∈ lifts (show D.obj j →+* c.pt from (c.ι.app j).hom) := by
  classical
  choose j y hy using fun n => Concrete.isColimit_exists_rep D hc (f.coeff n)
  obtain ⟨S, hS⟩ := IsFiltered.sup_objs_exists (f.support.image j)
  refine ⟨S, (lifts_iff_coeff_lifts _).2 fun n => ?_⟩
  by_cases hn : n ∈ f.support
  · obtain ⟨g⟩ := hS (Finset.mem_image_of_mem j hn)
    exact ⟨(D.map g).hom (y n), (congrArg (fun t => t.hom (y n)) (c.w g)).trans (hy n)⟩
  · exact ⟨0, (map_zero _).trans (notMem_support_iff.1 hn).symm⟩

/- English proof (translation)
Introduce `J _ _ D c hc e hF hs f hf ω h0 h1`. Take `⟨j, hj⟩` from `exists_lift D c hc f`. Take `⟨g, rfl, -, hg⟩` from `lifts_and_natDegree_eq_and_monic hj hf`. Set `ej : D.obj j →+* e.pt` to `(e.ι.app j).hom`. Set `cj : D.obj j →+* c.pt` to `(c.ι.app j).hom`.

Establish `hy : (hc.desc e).hom.comp cj = ej` using `congrArg (fun t => t.hom) (hc.fac e j)`. Express the relevant statement in the definitionally equal form `(g.map cj).eval₂ _ ω = 0 at h0`. Express the relevant statement in the definitionally equal form `(g.map cj).derivative.eval₂ _ ω ≠ 0 at h1`. Rewrite `h0` using `[eval₂_map, hy]`. Rewrite `h1` using `[derivative_map, eval₂_map, hy]`.

Set `P : StandardEtalePair (D.obj j)` to `⟨g, hg, g.derivative, 1, 0, 1, by simp⟩`. Set `_ : Algebra (D.obj j) e.pt` to `ej.toAlgebra`. Establish `hP : P.HasMap ω`. Take `⟨b, hb⟩` from `hF.mul_inv_cancel h1`. Conclude with `⟨h0, IsUnit.of_mul_eq_one b hb⟩`.

Take `⟨k, t, γ, h2, h3⟩` from `hs j (CommRingCat.of P.Ring) (CommRingCat.ofHom (algebraMap _ _)) (CommRingCat.ofHom (P.lift ω hP).toRingHom) (RingHom.etale_algebraMap.2 inferInstance) (CommRingCat.hom_ext (P.lift ω hP).comp_algebraMap)`. Set `ck : D.obj k →+* c.pt` to `(c.ι.app k).hom`. Set `γ' : P.Ring →+* D.obj k` to `γ.hom`. Establish `h4 : (ck.comp γ').comp (algebraMap (D.obj j) P.Ring) = cj`. Establish `: (CommRingCat.ofHom (algebraMap (D.obj j) P.Ring) ≫ γ) ≫ c.ι.app k = c.ι.app j` using `by rw [h2]; exact c.w t`.

Conclude with `congrArg (fun t => t.hom) this`. Use `⟨(ck.comp γ') P.X, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(g.map cj).eval _ = 0`. Establish `h5 : g.eval₂ (algebraMap (D.obj j) P.Ring) P.X = 0` using `P.hasMap_X.1`. Rewrite using `[Polynomial.eval_map, ← h4, ← hom_eval₂, h5, map_zero]`.

Establish `h6 : (hc.desc e).hom (ck (γ' P.X)) = (e.ι.app k).hom (γ' P.X)` using `congrArg (fun t => t.hom (γ' P.X)) (hc.fac e k)`. Establish `h7 : (e.ι.app k).hom (γ' P.X) = P.lift ω hP P.X` using `congrArg (fun t => t.hom P.X) h3`. Conclude with `h6.trans (h7.trans (P.lift_X ω hP))`.
-/
theorem satRoot : SatRoot := by
  intro J _ _ D c hc e hF hs f hf ω h0 h1
  obtain ⟨j, hj⟩ := exists_lift D c hc f
  obtain ⟨g, rfl, -, hg⟩ := lifts_and_natDegree_eq_and_monic hj hf
  let ej : D.obj j →+* e.pt := (e.ι.app j).hom
  let cj : D.obj j →+* c.pt := (c.ι.app j).hom
  have hy : (hc.desc e).hom.comp cj = ej := congrArg (fun t => t.hom) (hc.fac e j)
  change (g.map cj).eval₂ _ ω = 0 at h0
  change (g.map cj).derivative.eval₂ _ ω ≠ 0 at h1
  rw [eval₂_map, hy] at h0
  rw [derivative_map, eval₂_map, hy] at h1
  let P : StandardEtalePair (D.obj j) := ⟨g, hg, g.derivative, 1, 0, 1, by simp⟩
  let _ : Algebra (D.obj j) e.pt := ej.toAlgebra
  have hP : P.HasMap ω := by
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel h1
    exact ⟨h0, IsUnit.of_mul_eq_one b hb⟩
  obtain ⟨k, t, γ, h2, h3⟩ := hs j (CommRingCat.of P.Ring) (CommRingCat.ofHom (algebraMap _ _))
    (CommRingCat.ofHom (P.lift ω hP).toRingHom) (RingHom.etale_algebraMap.2 inferInstance)
    (CommRingCat.hom_ext (P.lift ω hP).comp_algebraMap)
  let ck : D.obj k →+* c.pt := (c.ι.app k).hom
  let γ' : P.Ring →+* D.obj k := γ.hom
  have h4 : (ck.comp γ').comp (algebraMap (D.obj j) P.Ring) = cj := by
    have : (CommRingCat.ofHom (algebraMap (D.obj j) P.Ring) ≫ γ) ≫ c.ι.app k = c.ι.app j := by rw [h2]; exact c.w t
    exact congrArg (fun t => t.hom) this
  refine ⟨(ck.comp γ') P.X, ?_, ?_⟩
  · change (g.map cj).eval _ = 0
    have h5 : g.eval₂ (algebraMap (D.obj j) P.Ring) P.X = 0 := P.hasMap_X.1
    rw [Polynomial.eval_map, ← h4, ← hom_eval₂, h5, map_zero]
  · have h6 : (hc.desc e).hom (ck (γ' P.X)) = (e.ι.app k).hom (γ' P.X) := congrArg (fun t => t.hom (γ' P.X)) (hc.fac e k)
    have h7 : (e.ι.app k).hom (γ' P.X) = P.lift ω hP P.X := congrArg (fun t => t.hom P.X) h3
    exact h6.trans (h7.trans (P.lift_X ω hP))

/- English proof (translation)
Introduce `C Ω _ _ _ ε hu hr`. Establish `: Nontrivial C` using `ε.domain_nontrivial`. Establish `: IsLocalRing C` using `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by`. Distinguish the cases in `h : ε a = 0`. Conclude with `Or.inr (hu _ (by simp [h]))`.

Conclude with `Or.inl (hu _ h)`. Establish `hm : ∀ x, x ∈ IsLocalRing.maximalIdeal C ↔ ε x = 0` using `fun x => by`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `⟨fun h => by_contra fun h' => h (hu x h'), fun h h' => (h'.map ε).ne_zero h⟩`. Establish `: IsLocalHom ε` using `⟨fun a ha => hu a ha.ne_zero⟩`.

Use `⟨{ is_henselian := fun f hf a₀ h0 h1 => ?_ }, IsSepClosed.of_exists_root _ fun p hp hi hsep => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, ha'⟩` from `hr f hf (ε a₀) (by rw [eval₂_at_apply]; exact (hm _).1 h0) (by rw [eval₂_at_apply]; exact (h1.map ε).ne_zero)`. Conclude with `⟨a, ha, (hm _).2 (by rw [map_sub, ha', sub_self])⟩`. Set `ι` to `IsLocalRing.ResidueField.lift ε`. Establish `hι : ι.comp (IsLocalRing.residue C) = ε` using `IsLocalRing.ResidueField.lift_comp_residue ε`.

Take `⟨ω, hω⟩` from `IsAlgClosed.exists_eval₂_eq_zero_of_injective ι ι.injective p hi.degree_pos.ne'`. Establish `hd` using `hsep.eval₂_derivative_ne_zero ι hω`. Take `⟨f, rfl, -, hf⟩` from `lifts_and_natDegree_eq_and_monic (f := IsLocalRing.residue C) ((lifts_iff_coeff_lifts p).2 fun n => IsLocalRing.residue_surjective _) hp`. Rewrite `hω` using `[eval₂_map, hι]`. Rewrite `hd` using `[derivative_map, eval₂_map, hι]`.

Take `⟨a, ha, -⟩` from `hr f hf ω hω hd`. Conclude with `⟨IsLocalRing.residue C a, by rw [Polynomial.eval_map, eval₂_at_apply, ha.eq_zero, map_zero]⟩`.
-/
theorem shOfLift : SHOfLift := by
  intro C Ω _ _ _ ε hu hr
  have : Nontrivial C := ε.domain_nontrivial
  have : IsLocalRing C := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases h : ε a = 0
    · exact Or.inr (hu _ (by simp [h]))
    · exact Or.inl (hu _ h)
  have hm : ∀ x, x ∈ IsLocalRing.maximalIdeal C ↔ ε x = 0 := fun x => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h => by_contra fun h' => h (hu x h'), fun h h' => (h'.map ε).ne_zero h⟩
  have : IsLocalHom ε := ⟨fun a ha => hu a ha.ne_zero⟩
  refine ⟨{ is_henselian := fun f hf a₀ h0 h1 => ?_ }, IsSepClosed.of_exists_root _ fun p hp hi hsep => ?_⟩
  · obtain ⟨a, ha, ha'⟩ := hr f hf (ε a₀) (by rw [eval₂_at_apply]; exact (hm _).1 h0)
      (by rw [eval₂_at_apply]; exact (h1.map ε).ne_zero)
    exact ⟨a, ha, (hm _).2 (by rw [map_sub, ha', sub_self])⟩
  · let ι := IsLocalRing.ResidueField.lift ε
    have hι : ι.comp (IsLocalRing.residue C) = ε := IsLocalRing.ResidueField.lift_comp_residue ε
    obtain ⟨ω, hω⟩ := IsAlgClosed.exists_eval₂_eq_zero_of_injective ι ι.injective p hi.degree_pos.ne'
    have hd := hsep.eval₂_derivative_ne_zero ι hω
    obtain ⟨f, rfl, -, hf⟩ := lifts_and_natDegree_eq_and_monic (f := IsLocalRing.residue C)
      ((lifts_iff_coeff_lifts p).2 fun n => IsLocalRing.residue_surjective _) hp
    rw [eval₂_map, hι] at hω
    rw [derivative_map, eval₂_map, hι] at hd
    obtain ⟨a, ha, -⟩ := hr f hf ω hω hd
    exact ⟨IsLocalRing.residue C a, by rw [Polynomial.eval_map, eval₂_at_apply, ha.eq_zero, map_zero]⟩

/- English proof (translation)
The claim follows from `goal_of satUnit satRoot shOfLift`.
-/
theorem shen : LateralTheory.KummerTheory.StrictHenselization := goal_of satUnit satRoot shOfLift

end LateralTheory.KummerTheory.SHenCut

end
