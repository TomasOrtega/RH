import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafMapMonoEpiIsoStatement

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

private def sumP (P₁ P₂ : PSh) : PSh where
  obj U := P₁.obj U ⊕ P₂.obj U
  map h := TypeCat.ofHom (Sum.map (P₁.map h) (P₂.map h))
  map_id U := by
    ext x
    rcases x with x | x <;> simp
  map_comp a b := by
    ext x
    rcases x with x | x <;> simp

private def sumD {P₁ P₂ Q : PSh} (f : P₁ ⟶ Q) (g : P₂ ⟶ Q) : sumP P₁ P₂ ⟶ Q where
  app U := TypeCat.ofHom (Sum.elim (f.app U) (g.app U))
  naturality U V k := by
    ext x
    rcases x with x | x
    · exact congrFun (congrArg (fun t => t.hom) (f.naturality k)) x
    · exact congrFun (congrArg (fun t => t.hom) (g.naturality k)) x

/- English proof (translation)
Introduce `R _ P₁ P₂ Q f g h`. Establish `mc : ∀ {P : PSh} (c : P ⟶ Q) {M : Shv R} (p : (free R).obj Q ⟶ M) (T : Scheme.{0}) (x : P.obj (op T)), Sec.map ((free R).map c ≫ p) (freeGen R P T x) = Sec.map p (freeGen R Q T (c.app (op T) x))`. Introduce `P c M p T x`. Establish `h4` using `(GlobalTheory.T.free_sections_ext_res_map R P M).2.2.2 Q c T x`. Use `show Sec.map p (Sec.map ((free R).map c) (freeGen R P T x)) = _`.

Rewrite using `[h4]`. Establish `hE : Epi ((free R).map (sumD f g))`. Apply `(GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R (sumD f g)).2.1` to reduce the goal to its premises. Introduce `T y`. Take `⟨S, hS, hP⟩` from `h T y`.

Use `⟨S, hS, fun W k hk => ?_⟩` and prove the remaining obligations. Break down `hP W k hk with ⟨x, hx⟩ | ⟨x, hx⟩` into its components or cases. Conclude with `⟨Sum.inl x, hx⟩`. Conclude with `⟨Sum.inr x, hx⟩`. Prove the components needed by the constructor for the conclusion.

Introduce `Z u v huv`. Establish `ha : (free R).map f ≫ u = (free R).map f ≫ v`. Simplify using `using congrArg (biprod.inl ≫ ·) huv`. Establish `hb : (free R).map g ≫ u = (free R).map g ≫ v`. Simplify using `using congrArg (biprod.inr ≫ ·) huv`.

Rewrite using `[← cancel_epi ((free R).map (sumD f g))]`. Apply `(GlobalTheory.T.free_sections_ext_res_map R (sumP P₁ P₂) Z).2.1` to reduce the goal to its premises. Introduce `T z`. Rewrite using `[mc, mc]`. Consider the cases of `z with`.

Consider the case `inl x`. Establish `e` using `mc f u T x`. Establish `e'` using `mc f v T x`. Rewrite `e` using `[ha]`. Conclude with `e.symm.trans e'`.

Consider the case `inr x`. Establish `e` using `mc g u T x`. Establish `e'` using `mc g v T x`. Rewrite `e` using `[hb]`. Conclude with `e.symm.trans e'`.
-/
theorem UpperTheory.epi_freeBiprodDesc_of_zariskiLocally_surjective :
    ∀ (R : Type) [CommRing R] {P₁ P₂ Q : PSh} (f : P₁ ⟶ Q) (g : P₂ ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V h => (∃ x, f.app (op V) x = Q.map h.op y) ∨ ∃ x, g.app (op V) x = Q.map h.op y) → Epi (biprod.desc ((free R).map f) ((free R).map g)) := by
  intro R _ P₁ P₂ Q f g h
  have mc : ∀ {P : PSh} (c : P ⟶ Q) {M : Shv R} (p : (free R).obj Q ⟶ M) (T : Scheme.{0})
      (x : P.obj (op T)),
      Sec.map ((free R).map c ≫ p) (freeGen R P T x) = Sec.map p (freeGen R Q T (c.app (op T) x)) := by
    intro P c M p T x
    have h4 := (GlobalTheory.T.free_sections_ext_res_map R P M).2.2.2 Q c T x
    show Sec.map p (Sec.map ((free R).map c) (freeGen R P T x)) = _
    rw [h4]
  have hE : Epi ((free R).map (sumD f g)) := by
    apply (GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R (sumD f g)).2.1
    intro T y
    obtain ⟨S, hS, hP⟩ := h T y
    refine ⟨S, hS, fun W k hk => ?_⟩
    rcases hP W k hk with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr x, hx⟩
  constructor
  intro Z u v huv
  have ha : (free R).map f ≫ u = (free R).map f ≫ v := by
    simpa using congrArg (biprod.inl ≫ ·) huv
  have hb : (free R).map g ≫ u = (free R).map g ≫ v := by
    simpa using congrArg (biprod.inr ≫ ·) huv
  rw [← cancel_epi ((free R).map (sumD f g))]
  apply (GlobalTheory.T.free_sections_ext_res_map R (sumP P₁ P₂) Z).2.1
  intro T z
  rw [mc, mc]
  cases z with
  | inl x =>
    have e := mc f u T x
    have e' := mc f v T x
    rw [ha] at e
    exact e.symm.trans e'
  | inr x =>
    have e := mc g u T x
    have e' := mc g v T x
    rw [hb] at e
    exact e.symm.trans e'
