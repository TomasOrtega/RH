import Development.EtaleCohomology.EtaleSheaves.ChartSurjCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ChartSurjCut

namespace LateralTheory.E.LCIsoPf

def TwTriv : Prop := ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)),
  ∃ e : ∀ (X : Scheme.{0}) (_s : X ⟶ S), Sec (tw q 0) X ≃+ Sec (tw q i) X,
    ∀ {X Y : Scheme.{0}} (s : X ⟶ S) (t : Y ⟶ S) (f : Y ⟶ X), f ≫ s = t → ∀ x : Sec (tw q 0) X,
      Sec.res f (e X s x) = e Y t (Sec.res f x)

def Tw0 : Prop := ∀ (q : ℕ),
  ∃ c : ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → (LocallyConstant T (ZMod q) ≃+ Sec (tw q 0) T),
    ∀ {V U : Scheme.{0}} (g : V ⟶ U) (hV : IsUnit (q : Γ(V, ⊤))) (hU : IsUnit (q : Γ(U, ⊤))) (a : LocallyConstant U (ZMod q)),
      Sec.res g (c U hU a) = c V hV (a.comap g.base.hom)

def SecIso : Prop := ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)),
  ∃ e : ∀ (X : Scheme.{0}) (_s : X ⟶ S), LocallyConstant X (ZMod q) ≃+ Sec (tw q i) X,
    ∀ {X Y : Scheme.{0}} (s : X ⟶ S) (t : Y ⟶ S) (f : Y ⟶ X), f ≫ s = t → ∀ g : LocallyConstant X (ZMod q),
      Sec.res f (e X s g) = e Y t (g.comap f.base.hom)

/- English proof (translation)
The claim follows from `(ζ.map s.appTop.hom).2.1`.
-/
theorem unit_of {q : ℕ} {S X : Scheme.{0}} (ζ : Prim q Γ(S, ⊤)) (s : X ⟶ S) : IsUnit (q : Γ(X, ⊤)) :=
  (ζ.map s.appTop.hom).2.1

/- English proof (translation)
Introduce `q i S ζ`. Take `⟨eT, heT⟩` from `hT q i S ζ`. Take `⟨c, hc⟩` from `h0 q`. Use `⟨fun X s => (c X (unit_of ζ s)).trans (eT X s), ?_⟩` and prove the remaining obligations. Introduce `X Y s t f hf g`.

Simplify using `only [AddEquiv.trans_apply]`. Rewrite using `[heT s t f hf, hc f (unit_of ζ t) (unit_of ζ s)]`.
-/
theorem SecIso_of (hT : TwTriv) (h0 : Tw0) : SecIso := by
  intro q i S ζ
  obtain ⟨eT, heT⟩ := hT q i S ζ
  obtain ⟨c, hc⟩ := h0 q
  refine ⟨fun X s => (c X (unit_of ζ s)).trans (eT X s), ?_⟩
  intro X Y s t f hf g
  simp only [AddEquiv.trans_apply]
  rw [heT s t f hf, hc f (unit_of ζ t) (unit_of ζ s)]

/- English proof (translation)
Introduce `H q i S ζ`. Take `⟨eS, heS⟩` from `hS q i S ζ`. Take `⟨-, eA, heA, -⟩` from `H.a9 (ZMod q) (tw q i)`. Use `⟨fun X s => (eS X s).trans (eA X), ?_⟩` and prove the remaining obligations. Introduce `X Y s t f hf g`.

Simplify using `only [AddEquiv.trans_apply]`. Rewrite using `[heA, heS s t f hf g]`.
-/
theorem SecIso_LCIso (hS : SecIso) : LCIso := by
  intro H q i S ζ
  obtain ⟨eS, heS⟩ := hS q i S ζ
  obtain ⟨-, eA, heA, -⟩ := H.a9 (ZMod q) (tw q i)
  refine ⟨fun X s => (eS X s).trans (eA X), ?_⟩
  intro X Y s t f hf g
  simp only [AddEquiv.trans_apply]
  rw [heA, heS s t f hf g]

end LateralTheory.E.LCIsoPf
