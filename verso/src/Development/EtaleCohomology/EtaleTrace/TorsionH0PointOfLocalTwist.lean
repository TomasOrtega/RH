import Development.EtaleCohomology.EtaleTrace.EtaleTateTwistSectionsDeterminedByPointsOfProper
import Development.EtaleCohomology.TateTwists.StrictHenselianAcyclic

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.EtaleTrace

def PtCover : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] (T : Sieve (S k)), T ∈ Scheme.etaleTopology (S k) → T.arrows (𝟙 _)

def TwZero : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), twGen (q := q) 0 ζ = twGen 0 ξ

def EvNat : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X U : Scheme.{0}) (α : CochainComplex.HomComplex.Cochain ((chains R).obj (sch.obj X)) (res R F) 0)
  (x : U ⟶ X), ev α 0 0 (by simp) U x = Sec.res x (ev α 0 0 (by simp) X (𝟙 X))

def CocEq : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
  (α β : CochainComplex.HomComplex.Cocycle ((chains R).obj (sch.obj X)) (res R F) 0),
  (∀ (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U), ev α.1 0 0 (by simp) U x = ev β.1 0 0 (by simp) U x) → α = β

/- English proof (translation)
Establish `hq : 0 < l ^ j` using `pow_pos (Fact.out : l.Prime).pos j`. Take `⟨r, hr⟩` from `IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ j) k) (Polynomial.degree_cyclotomic_pos (l ^ j) k hq).ne'`. Establish `hu : IsUnit ((l ^ j : ℕ) : k)`. Rewrite using `[Nat.cast_pow]`. Conclude with `(isUnit_iff_ne_zero.2 hl).pow j`.

Establish `hr' : Polynomial.aeval r (Polynomial.cyclotomic (l ^ j) ℤ) = 0`. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]`. Conclude with `hr`. Conclude with `⟨Prim.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom ⟨r, hu, hr'⟩⟩`.
-/
theorem exists_prim (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] (hl : (l : k) ≠ 0) (j : ℕ) :
    Nonempty (Prim (l ^ j) Γ(S k, ⊤)) := by
  have hq : 0 < l ^ j := pow_pos (Fact.out : l.Prime).pos j
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ j) k)
    (Polynomial.degree_cyclotomic_pos (l ^ j) k hq).ne'
  have hu : IsUnit ((l ^ j : ℕ) : k) := by
    rw [Nat.cast_pow]; exact (isUnit_iff_ne_zero.2 hl).pow j
  have hr' : Polynomial.aeval r (Polynomial.cyclotomic (l ^ j) ℤ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hr
  exact ⟨Prim.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom ⟨r, hu, hr'⟩⟩

/- English proof (translation)
Introduce `hB l _ k _ _ hl j`. Use `haveI : NeZero (l ^ j) := ⟨(pow_pos (Fact.out : l.Prime).pos j).ne'⟩`. Take `⟨ζ⟩` from `exists_prim l k hl j`. Take `⟨-, e, he, hα⟩` from `base_gives_h0_locally_constant hB (ZMod (l ^ j)) (tw (l ^ j) 0)`. Take `⟨T1, T2, T3⟩` from `hTw (l ^ j) 0`.

Establish `hone : one (l ^ j) (sch.obj (S k)) = e _ (twGen 0 ζ)`. Take `⟨α, hαc, hαev⟩` from `hα (S k) (twGen 0 ζ)`. Establish `hprop : ∀ (U : Scheme.{0}) (x : Sx (sch.obj (S k)) 0 U) (ξ : Prim (l ^ j) Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ξ`. Introduce `U x ξ`. Establish `h1` using `hE (ZMod (l ^ j)) (tw (l ^ j) 0) (S k) U α.1 x`.

Rewrite using `[h1, hαev]`. Express the relevant statement in the definitionally equal form `Sec.res x (Sec.map (resι _ (tw (l ^ j) 0)) (twGen 0 ζ)) = Sec.map (resι _ (tw (l ^ j) 0)) (twGen 0 ξ)`. Establish `h2 : Sec.res x (Sec.map (resι _ (tw (l ^ j) 0)) (twGen 0 ζ)) = Sec.map (resι _ (tw (l ^ j) 0)) (Sec.res x (twGen 0 ζ))`. Simplify using `only [Sec.res, Sec.map]`. Rewrite using `[← ModuleCat.comp_apply, ← ModuleCat.comp_apply, NatTrans.naturality]`.

Rewrite using `[h2]`. Conclude with `(congrArg (Sec.map (resι _ (tw (l ^ j) 0))) (T3 U (S k) x ζ)).trans (congrArg (Sec.map (resι _ (tw (l ^ j) 0))) (hZ _ U _ ξ))`. Establish `hex : ∃ c, ∃ α' : CochainComplex.HomComplex.Cocycle _ _ 0, CohomologyClass.mk α' = c ∧ ∀ (U : Scheme.{0}) (x : Sx (sch.obj (S k)) 0 U) (ξ : Prim (l ^ j) Γ(U, ⊤)), ev α'.1 0 0 (by simp) U x = resGen 0 ξ` using `⟨_, α, rfl, hprop⟩`. Take `⟨α', hα'c, hα'ev⟩` from `pick_spec hex`. Establish `: α' = α` using `hQ _ _ (S k) α' α fun U x => by`.

Take `⟨ξ⟩ : Nonempty (Prim (l ^ j) Γ(U, ⊤))` from `⟨ζ.map (Scheme.Hom.appTop x).hom⟩`. Rewrite using `[hα'ev U x ξ, hprop U x ξ]`. Unfold `one`. Rewrite using `[← hα'c, this, hαc]`. Establish `hsec : ∀ s : Sec (tw (l ^ j) 0) (S k), ∃ c : ℕ, s = c • twGen 0 ζ`.

Introduce `s`. Take `⟨T, hT, hP⟩` from `T1 (S k) ζ s`. Take `⟨c, hc⟩` from `hP (S k) (𝟙 _) (hC k T hT)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hid : Sec.res (𝟙 (S k)) s = s` using `by simp [Sec.res]`.

Rewrite using `[← hid, hc, hZ _ _ _ ζ]`. Use `⟨fun z => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨s, rfl⟩` from `(e _).surjective z`. Take `⟨c, rfl⟩` from `hsec s`. Conclude with `⟨c, by rw [map_nsmul, hone]⟩`.

Rewrite `ha` using `[hone, ← map_nsmul, (e _).map_eq_zero_iff]`. Conclude with `T2 (S k) ζ a ha`.
-/
theorem torsion_h0_point_of_local_twist (hTw : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hC : PtCover) (hZ : TwZero) (hE : EvNat) (hQ : CocEq) : TorsionH0PointGenerated := by
  intro hB l _ k _ _ hl j
  haveI : NeZero (l ^ j) := ⟨(pow_pos (Fact.out : l.Prime).pos j).ne'⟩
  obtain ⟨ζ⟩ := exists_prim l k hl j
  obtain ⟨-, e, he, hα⟩ := base_gives_h0_locally_constant hB (ZMod (l ^ j)) (tw (l ^ j) 0)
  obtain ⟨T1, T2, T3⟩ := hTw (l ^ j) 0

  have hone : one (l ^ j) (sch.obj (S k)) = e _ (twGen 0 ζ) := by
    obtain ⟨α, hαc, hαev⟩ := hα (S k) (twGen 0 ζ)
    have hprop : ∀ (U : Scheme.{0}) (x : Sx (sch.obj (S k)) 0 U) (ξ : Prim (l ^ j) Γ(U, ⊤)),
        ev α.1 0 0 (by simp) U x = resGen 0 ξ := by
      intro U x ξ
      have h1 := hE (ZMod (l ^ j)) (tw (l ^ j) 0) (S k) U α.1 x
      rw [h1, hαev]
      change Sec.res x (Sec.map (resι _ (tw (l ^ j) 0)) (twGen 0 ζ)) = Sec.map (resι _ (tw (l ^ j) 0)) (twGen 0 ξ)
      have h2 : Sec.res x (Sec.map (resι _ (tw (l ^ j) 0)) (twGen 0 ζ)) =
          Sec.map (resι _ (tw (l ^ j) 0)) (Sec.res x (twGen 0 ζ)) := by
        simp only [Sec.res, Sec.map]
        rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, NatTrans.naturality]
      rw [h2]
      exact (congrArg (Sec.map (resι _ (tw (l ^ j) 0))) (T3 U (S k) x ζ)).trans (congrArg (Sec.map (resι _ (tw (l ^ j) 0))) (hZ _ U _ ξ))
    have hex : ∃ c, ∃ α' : CochainComplex.HomComplex.Cocycle _ _ 0, CohomologyClass.mk α' = c ∧
        ∀ (U : Scheme.{0}) (x : Sx (sch.obj (S k)) 0 U) (ξ : Prim (l ^ j) Γ(U, ⊤)),
          ev α'.1 0 0 (by simp) U x = resGen 0 ξ := ⟨_, α, rfl, hprop⟩
    obtain ⟨α', hα'c, hα'ev⟩ := pick_spec hex
    have : α' = α := hQ _ _ (S k) α' α fun U x => by
      obtain ⟨ξ⟩ : Nonempty (Prim (l ^ j) Γ(U, ⊤)) := ⟨ζ.map (Scheme.Hom.appTop x).hom⟩
      rw [hα'ev U x ξ, hprop U x ξ]
    unfold one
    rw [← hα'c, this, hαc]

  have hsec : ∀ s : Sec (tw (l ^ j) 0) (S k), ∃ c : ℕ, s = c • twGen 0 ζ := by
    intro s
    obtain ⟨T, hT, hP⟩ := T1 (S k) ζ s
    obtain ⟨c, hc⟩ := hP (S k) (𝟙 _) (hC k T hT)
    refine ⟨c, ?_⟩
    have hid : Sec.res (𝟙 (S k)) s = s := by simp [Sec.res]
    rw [← hid, hc, hZ _ _ _ ζ]
  refine ⟨fun z => ?_, fun a ha => ?_⟩
  · obtain ⟨s, rfl⟩ := (e _).surjective z
    obtain ⟨c, rfl⟩ := hsec s
    exact ⟨c, by rw [map_nsmul, hone]⟩
  · rw [hone, ← map_nsmul, (e _).map_eq_zero_iff] at ha
    exact T2 (S k) ζ a ha

end LateralTheory.EtaleTrace
