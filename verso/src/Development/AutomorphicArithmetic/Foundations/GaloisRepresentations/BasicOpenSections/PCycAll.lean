import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Apply `h` to reduce the goal to its premises. Establish `hu : IsUnit ((ConcreteCategory.hom (Scheme.Hom.app x ⊤)) (p : Γ(Y, ⊤)))`. Rewrite using `[map_natCast]`. Establish `e : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (p : Ω) = (p : Γ(gp Ω, ⊤))` using `map_natCast _ p`.

Establish `hu0` using `(IsUnit.mk0 _ hne).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom`. Rewrite `hu0` using `[e]`. Conclude with `hu0`. Establish `hpre` using `Scheme.preimage_basicOpen x (p : Γ(Y, ⊤))`. Rewrite `hpre` using `[Scheme.basicOpen_of_isUnit _ hu]`.

Establish `hm : IsLocalRing.closedPoint Ω ∈ x ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤))`. Rewrite using `[hpre]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `hm`.
-/
private lemma natCast_eq_zero_of_pt {p : ℕ} {Y : Scheme.{0}} {Ω : Type} [Field Ω] (x : gp Ω ⟶ Y)
    (h : pt x ∉ Y.basicOpen (p : Γ(Y, ⊤))) : (p : Ω) = 0 := by
  by_contra hne
  apply h
  have hu : IsUnit ((ConcreteCategory.hom (Scheme.Hom.app x ⊤)) (p : Γ(Y, ⊤))) := by
    rw [map_natCast]
    have e : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (p : Ω) = (p : Γ(gp Ω, ⊤)) := map_natCast _ p
    have hu0 := (IsUnit.mk0 _ hne).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
    rw [e] at hu0
    exact hu0
  have hpre := Scheme.preimage_basicOpen x (p : Γ(Y, ⊤))
  rw [Scheme.basicOpen_of_isUnit _ hu] at hpre
  have hm : IsLocalRing.closedPoint Ω ∈ x ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤)) := by
    rw [hpre]
    trivial
  exact hm

/- English proof (translation)
Conclude with `IsLocalRing.comap_closedPoint a`.
-/
private lemma sp_closedPoint {K L : Type} [Field K] [Field L] (a : K →+* L) :
    (sp a) (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint K := by
  exact IsLocalRing.comap_closedPoint a

/- English proof (translation)
Conclude with `IsLocalRing.comap_closedPoint (IsLocalRing.residue V)`.
-/
private lemma resPt_closedPoint (V : Type) [CommRing V] [IsLocalRing V] :
    (resPt V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) = IsLocalRing.closedPoint V := by
  exact IsLocalRing.comap_closedPoint (IsLocalRing.residue V)

/- English proof (translation)
Use `haveI : CharP F p := (CharP.charP_iff_prime_eq_zero hp).2 h`. Use `haveI : ExpChar F p := ExpChar.prime hp`. Conclude with `⟨iterateFrobenius F p f, fun a => iterateFrobenius_def p f a⟩`.
-/
private lemma exists_frob (p f : ℕ) (hp : p.Prime) (F : Type) [Field F] (h : (p : F) = 0) :
    ∃ φ : F →+* F, ∀ a, φ a = a ^ p ^ f := by
  haveI : CharP F p := (CharP.charP_iff_prime_eq_zero hp).2 h
  haveI : ExpChar F p := ExpChar.prime hp
  exact ⟨iterateFrobenius F p f, fun a => iterateFrobenius_def p f a⟩

/- English proof (translation)
Introduce `hRC hVL hCR hCE p f n hp Y π T w hOne hPt hdense hbasic Ω _ _ x hgen`. Take `⟨η, hη, hsp⟩` from `hdense (pt x)`. Take `⟨V, _, _, _, _, y, Ω', _, _, a, b, hpV, hsq⟩` from `hVL p Y Ω x η hsp hη`. Use `haveI := hRC V`. Establish `hx0 : pt x ∉ Y.basicOpen (p : Γ(Y, ⊤))` using `fun h => hgen.1 (hbasic _ h)`.

Establish `hptA : pt (sp a ≫ x) = pt x`. Express the relevant statement in the definitionally equal form `x (sp a (IsLocalRing.closedPoint Ω')) = _`. Rewrite using `[sp_closedPoint]`. Both sides reduce to the same expression. Establish `hptB : pt (sp b ≫ resPt V ≫ y) = y (IsLocalRing.closedPoint V)`.

Express the relevant statement in the definitionally equal form `y (resPt V (sp b (IsLocalRing.closedPoint Ω'))) = _`. Rewrite using `[sp_closedPoint, resPt_closedPoint]`. Establish `hyx : y (IsLocalRing.closedPoint V) = pt x`. Rewrite using `[← hptB, ← hsq, hptA]`. Establish `hpΩ` using `natCast_eq_zero_of_pt x hx0`.

Establish `hpΩ'` using `natCast_eq_zero_of_pt (sp a ≫ x) (by rw [hptA]; exact hx0)`. Establish `hpR` using `natCast_eq_zero_of_pt (resPt V ≫ y) (by`. Express the relevant statement in the definitionally equal form `y (resPt V (IsLocalRing.closedPoint _)) ∉ _`. Rewrite using `[resPt_closedPoint, hyx]`. Conclude with `hx0)`.

Take `⟨φ, hφ⟩` from `exists_frob p f hp Ω hpΩ`. Take `⟨φ', hφ'⟩` from `exists_frob p f hp Ω' hpΩ'`. Take `⟨ψ, hψ⟩` from `exists_frob p f hp (IsLocalRing.ResidueField V) hpR`. Use `⟨φ, hφ, ?_⟩` and prove the remaining obligations. Establish `hW : ∀ j, IsWt (T j).p (w j)` using `fun j => (hOne j).1`.

Establish `h1` using `hCR p (p ^ f) n Y π T w hOne hPt V hpV y (by rw [hyx]; exact hgen) ψ hψ`. Establish `h2` using `(hCE p (p ^ f) n Y T w hW _ Ω' b ψ φ' (RingHom.ext fun z => by simp [hψ, hφ', map_pow]) (resPt V ≫ y)).mp h1`. Rewrite `h2` using `[← hsq]`. Conclude with `(hCE p (p ^ f) n Y T w hW Ω Ω' a φ φ' (RingHom.ext fun z => by simp [hφ, hφ', map_pow]) x).mpr h2`.
-/
theorem UpperTheory.Gal.Mod.cycAll :
    ResClosed → ValLift → CycRes → CycExt → CycAll := by
  intro hRC hVL hCR hCE p f n hp Y π T w hOne hPt hdense hbasic Ω _ _ x hgen
  obtain ⟨η, hη, hsp⟩ := hdense (pt x)
  obtain ⟨V, _, _, _, _, y, Ω', _, _, a, b, hpV, hsq⟩ := hVL p Y Ω x η hsp hη
  haveI := hRC V
  have hx0 : pt x ∉ Y.basicOpen (p : Γ(Y, ⊤)) := fun h => hgen.1 (hbasic _ h)
  have hptA : pt (sp a ≫ x) = pt x := by
    change x (sp a (IsLocalRing.closedPoint Ω')) = _
    rw [sp_closedPoint]
    rfl
  have hptB : pt (sp b ≫ resPt V ≫ y) = y (IsLocalRing.closedPoint V) := by
    change y (resPt V (sp b (IsLocalRing.closedPoint Ω'))) = _
    rw [sp_closedPoint, resPt_closedPoint]
  have hyx : y (IsLocalRing.closedPoint V) = pt x := by
    rw [← hptB, ← hsq, hptA]
  have hpΩ := natCast_eq_zero_of_pt x hx0
  have hpΩ' := natCast_eq_zero_of_pt (sp a ≫ x) (by rw [hptA]; exact hx0)
  have hpR := natCast_eq_zero_of_pt (resPt V ≫ y) (by
    change y (resPt V (IsLocalRing.closedPoint _)) ∉ _
    rw [resPt_closedPoint, hyx]
    exact hx0)
  obtain ⟨φ, hφ⟩ := exists_frob p f hp Ω hpΩ
  obtain ⟨φ', hφ'⟩ := exists_frob p f hp Ω' hpΩ'
  obtain ⟨ψ, hψ⟩ := exists_frob p f hp (IsLocalRing.ResidueField V) hpR
  refine ⟨φ, hφ, ?_⟩
  have hW : ∀ j, IsWt (T j).p (w j) := fun j => (hOne j).1
  have h1 := hCR p (p ^ f) n Y π T w hOne hPt V hpV y (by rw [hyx]; exact hgen) ψ hψ
  have h2 := (hCE p (p ^ f) n Y T w hW _ Ω' b ψ φ'
    (RingHom.ext fun z => by simp [hψ, hφ', map_pow]) (resPt V ≫ y)).mp h1
  rw [← hsq] at h2
  exact (hCE p (p ^ f) n Y T w hW Ω Ω' a φ φ'
    (RingHom.ext fun z => by simp [hφ, hφ', map_pow]) x).mpr h2
