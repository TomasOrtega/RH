import Development.EtaleCohomology.TateTwists.EtaleKummerTriangleExists

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

def EtaleKummerSectionsIntoTwistEmbeddingExist : Prop :=
  ∀ (q : ℕ) [NeZero q], ∃ (M : Shv (ZMod q)) (j : tw q 1 ⟶ M), Mono j ∧
    ∃ s : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec M U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) →
        Sec.res g (s U v) = s V (Units.map g.appTop.hom.toMonoidHom v)) ∧
      ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (v w : (Γ(U, ⊤))ˣ), (w : Γ(U, ⊤)) = ζ.1 * v →
        s U w = s U v + Sec.map j (twGen 1 ζ)

def EtaleTwistExtendsThroughMonoToResolutionZero : Prop :=
  ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) (j : tw q 1 ⟶ M), Mono j →
    ∃ e : M ⟶ (res _ (tw q 1)).X 0, j ≫ e = resι _ (tw q 1)

/- English proof (translation)
Introduce `q _`. Apply `pick_spec` to reduce the goal to its premises. Take `⟨M, j, hj, s, hs1, hs2⟩` from `h1 q`. Take `⟨e, he⟩` from `h2 q M j hj`. Use `⟨fun U v => Sec.map e (s U v), ?_, ?_⟩` and prove the remaining obligations.

Introduce `V U g v hq show Sec.res g (Sec.map e (s U v)) = Sec.map e (s V _)`. Rewrite using `[← hs1 V U g v hq]`. Conclude with `(LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (e.hom.naturality g.op)) (s U v)).symm`. Introduce `U ζ v w h show Sec.map e (s U w) = Sec.map e (s U v) + _`. Rewrite using `[hs2 U ζ v w h]`.

Use `show (e.hom.app (op U)).hom (_ + _) = _`. Rewrite using `[map_add]`. Use `congr 1`. Unfold `resGen`. Rewrite using `[← he]`.

Both sides reduce to the same expression.
-/
theorem etale_kummer_torsor_class_exists_of_tors_and_ext (h1 : EtaleKummerSectionsIntoTwistEmbeddingExist) (h2 : EtaleTwistExtendsThroughMonoToResolutionZero) : EtaleKummerTriangleExists := by
  intro q _
  apply pick_spec
  obtain ⟨M, j, hj, s, hs1, hs2⟩ := h1 q
  obtain ⟨e, he⟩ := h2 q M j hj
  refine ⟨fun U v => Sec.map e (s U v), ?_, ?_⟩
  · intro V U g v hq
    show Sec.res g (Sec.map e (s U v)) = Sec.map e (s V _)
    rw [← hs1 V U g v hq]
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (e.hom.naturality g.op)) (s U v)).symm
  · intro U ζ v w h
    show Sec.map e (s U w) = Sec.map e (s U v) + _
    rw [hs2 U ζ v w h]
    show (e.hom.app (op U)).hom (_ + _) = _
    rw [map_add]
    congr 1
    unfold resGen
    rw [← he]
    rfl
end LateralTheory.EtaleFoundations
