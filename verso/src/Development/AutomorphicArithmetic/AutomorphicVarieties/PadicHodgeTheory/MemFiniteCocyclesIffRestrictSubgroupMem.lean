import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fDescAvg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

/- English proof (translation)
Introduce `l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT β hβ`. Use `haveI := hD.normal`. Use `haveI := hD.fin`. Establish `hM : ∀ (g : H) (v : B × B), (T.M1.comp H.subtype : Representation B H (B × B)) g v = (chRep (T.ch H hD.ηH 0 / T.ch H hD.ηH 1) g v.1, chRep (T.ch H hD.ηH 1 / T.ch H hD.ηH 2) g v.2)`. Introduce `g v`.

Express the relevant statement in the definitionally equal form `T.M1 g v = _`. Rewrite using `[Tor.adjointSuperdiagRep_apply, if_pos (hD.ηH g g.2)]`. Both sides reduce to the same expression. Rewrite using `[z1fDesc (MonoidHom.id (GQ l)) T.M1 H β hβ, MonoidHom.id_comp]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `⟨(z1fMap H.subtype _ _).2 (LinearMap.fst ℚ_[l] B B) (fun g x => by rw [hM]; rfl) _ h, (z1fMap H.subtype _ _).2 (LinearMap.snd ℚ_[l] B B) (fun g x => by rw [hM]; rfl) _ h⟩`. Introduce and unpack `⟨h1, h2⟩`. Establish `k1` using `(z1fMap H.subtype _ (T.M1.comp H.subtype : Representation B H (B × B))).2 (LinearMap.inl ℚ_[l] B B) (fun g x => by rw [hM]; simp) _ h1`. Establish `k2` using `(z1fMap H.subtype _ (T.M1.comp H.subtype : Representation B H (B × B))).2 (LinearMap.inr ℚ_[l] B B) (fun g x => by rw [hM]; simp) _ h2`.

Establish `k` using `add_mem k1 k2`. Use `k using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.mem_finiteCocycles_iff_restrict_subgroup_mem :
    ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B), T.Good π Ψ → ∀ β ∈ Z1 T.M1, (β ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T.M1 ↔ (fun g : H => (β g).1) ∈ UpperTheory.V.Loc.finiteCocycles H.subtype (chRep (T.ch H hD.ηH 0 / T.ch H hD.ηH 1)) ∧ (fun g : H => (β g).2) ∈ UpperTheory.V.Loc.finiteCocycles H.subtype (chRep (T.ch H hD.ηH 1 / T.ch H hD.ηH 2))) := by
  intro l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT β hβ
  haveI := hD.normal
  haveI := hD.fin
  have hM : ∀ (g : H) (v : B × B), (T.M1.comp H.subtype : Representation B H (B × B)) g v =
      (chRep (T.ch H hD.ηH 0 / T.ch H hD.ηH 1) g v.1, chRep (T.ch H hD.ηH 1 / T.ch H hD.ηH 2) g v.2) := by
    intro g v
    change T.M1 g v = _
    rw [Tor.adjointSuperdiagRep_apply, if_pos (hD.ηH g g.2)]
    rfl
  rw [z1fDesc (MonoidHom.id (GQ l)) T.M1 H β hβ, MonoidHom.id_comp]
  constructor
  · intro h
    exact ⟨(z1fMap H.subtype _ _).2 (LinearMap.fst ℚ_[l] B B) (fun g x => by rw [hM]; rfl) _ h,
      (z1fMap H.subtype _ _).2 (LinearMap.snd ℚ_[l] B B) (fun g x => by rw [hM]; rfl) _ h⟩
  · rintro ⟨h1, h2⟩
    have k1 := (z1fMap H.subtype _ (T.M1.comp H.subtype : Representation B H (B × B))).2
      (LinearMap.inl ℚ_[l] B B) (fun g x => by rw [hM]; simp) _ h1
    have k2 := (z1fMap H.subtype _ (T.M1.comp H.subtype : Representation B H (B × B))).2
      (LinearMap.inr ℚ_[l] B B) (fun g x => by rw [hM]; simp) _ h2
    have k := add_mem k1 k2
    convert k using 1
    funext g
    simp
