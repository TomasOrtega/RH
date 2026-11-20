import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdealStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ChartMaps

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

/- English proof (translation)
Introduce `x hx`. Distinguish the cases in `hp : p = 0`. Take `⟨n, hn⟩` from `T.adm.2 hp`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h : x ^ n ∈ T.J ^ n` using `Ideal.pow_mem_pow hx n`.

Rewrite `h` using `[hn]`. Conclude with `h`. Take `⟨n, hn⟩ : IsNilpotent ((p : ℕ) : T.B)` from `T.adm.1 hp`. Use `⟨p * n, ?_⟩` and prove the remaining obligations. Establish `h1 : x ^ p = (p.factorial : T.B) * T.δ.dpow p x` using `(T.δ.factorial_mul_dpow_eq_pow hx).symm`.

Establish `h2 : (p.factorial : T.B) = (p : T.B) * ((p - 1).factorial : T.B)`. Rewrite using `[← Nat.cast_mul, Nat.mul_factorial_pred hp]`. Rewrite using `[pow_mul, h1, h2, mul_assoc, mul_pow, hn, zero_mul]`.
-/
theorem nil_J (T : Thick (nlFun γ p X q κ)) : ∀ x ∈ T.J, IsNilpotent x := by
  intro x hx
  by_cases hp : p = 0
  · obtain ⟨n, hn⟩ := T.adm.2 hp
    refine ⟨n, ?_⟩
    have h : x ^ n ∈ T.J ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at h
    exact h
  · obtain ⟨n, hn⟩ : IsNilpotent ((p : ℕ) : T.B) := T.adm.1 hp
    refine ⟨p * n, ?_⟩
    have h1 : x ^ p = (p.factorial : T.B) * T.δ.dpow p x := (T.δ.factorial_mul_dpow_eq_pow hx).symm
    have h2 : (p.factorial : T.B) = (p : T.B) * ((p - 1).factorial : T.B) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred hp]
    rw [pow_mul, h1, h2, mul_assoc, mul_pow, hn, zero_mul]

/- English proof (translation)
Establish `e : f.comp c.D.i = T.i` using `RingHom.ext hf`. Use `IsDPMorphism.of_comp γ c.D.δ T.δ c.D.i f c.J_eq c.D.compat ?_` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `T.compat`.
-/
theorem isDP {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (T : Thick (nlFun γ p X q κ))
    (f : c.D.B →+* T.B) (hf : ∀ r, f (c.D.i r) = T.i r) : IsDPMorphism c.D.δ T.δ f := by
  have e : f.comp c.D.i = T.i := RingHom.ext hf
  refine IsDPMorphism.of_comp γ c.D.δ T.δ c.D.i f c.J_eq c.D.compat ?_
  rw [e]
  exact T.compat

/- English proof (translation)
Establish `hL` using `GlobalTheory.T.etale_lifting_of_nil_ideal T.J (nil_J T)`. Establish `hc : (g.comp (Ideal.Quotient.mk c.D.J)).comp (MvPolynomial.eval₂Hom c.D.i c.t : MvPolynomial (Fin d) R →+* c.D.B) = (Ideal.Quotient.mk T.J).comp (MvPolynomial.eval₂Hom T.i y : MvPolynomial (Fin d) R →+* T.B)`. Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)` and prove the remaining obligations. Simplify using `using hg r`. Simplify using `using (hy k).symm`.

Take `⟨f, ⟨h1, h2⟩, hu⟩` from `hL (MvPolynomial (Fin d) R) c.D.B _ c.etale (MvPolynomial.eval₂Hom T.i y) (g.comp (Ideal.Quotient.mk c.D.J)) hc`. Use `⟨f, ⟨fun r => ?_, fun k => ?_, h2⟩, ?_⟩` and prove the remaining obligations. Simplify using `using RingHom.congr_fun h1 (MvPolynomial.C r)`. Simplify using `using RingHom.congr_fun h1 (MvPolynomial.X k)`. Introduce and unpack `f' ⟨a1, a2, a3⟩`.

Use `hu f' ⟨MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_), a3⟩` and prove the remaining obligations. Simplify using `using a1 r`. Simplify using `using a2 k`.
-/
theorem exists_unique_lift {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d)
    (T : Thick (nlFun γ p X q κ)) (g : c.D.B ⧸ c.D.J →+* T.B ⧸ T.J)
    (hg : ∀ r, g (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (T.i r))
    (y : Fin d → T.B) (hy : ∀ k, Ideal.Quotient.mk T.J (y k) = g (Ideal.Quotient.mk _ (c.t k))) :
    ∃! f : c.D.B →+* T.B, (∀ r, f (c.D.i r) = T.i r) ∧ (∀ k, f (c.t k) = y k) ∧
      (Ideal.Quotient.mk T.J).comp f = g.comp (Ideal.Quotient.mk c.D.J) := by
  have hL := GlobalTheory.T.etale_lifting_of_nil_ideal T.J (nil_J T)
  have hc : (g.comp (Ideal.Quotient.mk c.D.J)).comp
      (MvPolynomial.eval₂Hom c.D.i c.t : MvPolynomial (Fin d) R →+* c.D.B) =
      (Ideal.Quotient.mk T.J).comp (MvPolynomial.eval₂Hom T.i y : MvPolynomial (Fin d) R →+* T.B) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
    · simpa using hg r
    · simpa using (hy k).symm
  obtain ⟨f, ⟨h1, h2⟩, hu⟩ := hL (MvPolynomial (Fin d) R) c.D.B _ c.etale
    (MvPolynomial.eval₂Hom T.i y) (g.comp (Ideal.Quotient.mk c.D.J)) hc
  refine ⟨f, ⟨fun r => ?_, fun k => ?_, h2⟩, ?_⟩
  · simpa using RingHom.congr_fun h1 (MvPolynomial.C r)
  · simpa using RingHom.congr_fun h1 (MvPolynomial.X k)
  · rintro f' ⟨a1, a2, a3⟩
    refine hu f' ⟨MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_), a3⟩
    · simpa using a1 r
    · simpa using a2 k

/- English proof (translation)
Establish `e : pt T = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.J σ.φ σ.hle)) ≫ pt c.D`. Unfold `pt`. Rewrite using `[← σ.pt]`. Both sides reduce to the same expression. Unfold `InU`.

Rewrite using `[e]`. Introduce `x _`. Conclude with `c.inV (show (Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.J σ.φ σ.hle))) x ∈ ⊤ from trivial)`.
-/
theorem inU_of_hom {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) {T : Thick (nlFun γ p X q κ)}
    (σ : c.D ⟶ T) : InU V T := by
  have e : pt T = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.J σ.φ σ.hle)) ≫ pt c.D := by
    unfold pt
    rw [← σ.pt]
    rfl
  unfold InU
  rw [e]
  intro x _
  exact c.inV (show (Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.J σ.φ σ.hle))) x ∈ ⊤ from trivial)

/- English proof (translation)
Establish `e` using `congrArg (fun z : PtOver X q κ (T.B ⧸ T.J) => z.1.1 (Ideal.Quotient.mk _ r)) hg`. Establish `w1` using `c.D.w r`. Establish `w2` using `T.w r`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem quot_comm {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (T : Thick (nlFun γ p X q κ))
    (g : c.D.B ⧸ c.D.J →+* T.B ⧸ T.J)
    (hg : (nlFun γ p X q κ).Pt.map (CommRingCat.ofHom g) c.D.y = T.y) (r : R) :
    g (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (T.i r) := by
  have e := congrArg (fun z : PtOver X q κ (T.B ⧸ T.J) => z.1.1 (Ideal.Quotient.mk _ r)) hg
  have w1 := c.D.w r
  have w2 := T.w r
  calc g (Ideal.Quotient.mk _ (c.D.i r))
      = g ((nlFun γ p X q κ).str c.D.y (Ideal.Quotient.mk _ r)) := by rw [w1]
    _ = (nlFun γ p X q κ).str T.y (Ideal.Quotient.mk _ r) := e
    _ = Ideal.Quotient.mk _ (T.i r) := w2

def homOf {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (T : Thick (nlFun γ p X q κ))
    (f : c.D.B →+* T.B) (hf : ∀ r, f (c.D.i r) = T.i r) (g : c.D.B ⧸ c.D.J →+* T.B ⧸ T.J)
    (hq : (Ideal.Quotient.mk T.J).comp f = g.comp (Ideal.Quotient.mk c.D.J))
    (hg : (nlFun γ p X q κ).Pt.map (CommRingCat.ofHom g) c.D.y = T.y) : c.D ⟶ T :=
  have hdp := isDP c T f hf
  have hle : c.D.J ≤ T.J.comap f := fun _ hx => hdp.1 (Ideal.mem_map_of_mem f hx)
  mkH f hf hdp hle (by
    have e : Ideal.quotientMap T.J f hle = g :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun x => RingHom.congr_fun hq x)
    rw [e]
    exact hg)

/- English proof (translation)
Use `⟨fun T hT => ?_, fun T σ y hy => ?_⟩` and prove the remaining obligations. Take `⟨g, hg, -⟩` from `c.rep (CommRingCat.of (T.B ⧸ T.J)) T.y hT`. Establish `hg' : (nlFun γ p X q κ).Pt.map (CommRingCat.ofHom g) c.D.y = T.y` using `hg`. Use `choose y hy using fun k => Ideal.Quotient.mk_surjective (g (Ideal.Quotient.mk _ (c.t k)))`. Take `⟨f, ⟨h1, -, h3⟩, -⟩` from `exists_unique_lift c T g (quot_comm c T g hg') y hy`.

Conclude with `⟨homOf c T f h1 g h3 hg'⟩`. Establish `hg : (nlFun γ p X q κ).Pt.map (CommRingCat.ofHom (Ideal.quotientMap T.J σ.φ σ.hle)) c.D.y = T.y` using `σ.pt`. Establish `hs : ∀ k, Ideal.Quotient.mk T.J (σ.φ (c.t k) + y k) = Ideal.quotientMap T.J σ.φ σ.hle (Ideal.Quotient.mk _ (c.t k))` using `fun k => by`. Rewrite using `[Ideal.quotientMap_mk, map_add, Ideal.Quotient.eq_zero_iff_mem.2 (hy k), add_zero]`. Take `⟨f, ⟨h1, h2, h3⟩, hu⟩` from `exists_unique_lift c T (Ideal.quotientMap T.J σ.φ σ.hle) (quot_comm c T _ hg) (fun k => σ.φ (c.t k) + y k) hs`.

Use `⟨homOf c T f h1 _ h3 hg, fun i => ?_, fun τ hτ => hom_ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f (c.t i) - σ.φ (c.t i) = y i`. Rewrite using `[h2 i]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨g₀, -, hu₀⟩` from `c.rep (CommRingCat.of (T.B ⧸ T.J)) T.y (inU_of_hom c σ)`.

Establish `e : Ideal.quotientMap T.J τ.φ τ.hle = Ideal.quotientMap T.J σ.φ σ.hle` using `(hu₀ _ τ.pt).trans (hu₀ _ σ.pt).symm`. Use `hu τ.φ ⟨τ.comm, fun k => ?_, ?_⟩` and prove the remaining obligations. Use `hτ k` as an intermediate fact. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← e]`. Both sides reduce to the same expression.
-/
theorem good {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) : c.Good := by
  refine ⟨fun T hT => ?_, fun T σ y hy => ?_⟩
  · obtain ⟨g, hg, -⟩ := c.rep (CommRingCat.of (T.B ⧸ T.J)) T.y hT
    have hg' : (nlFun γ p X q κ).Pt.map (CommRingCat.ofHom g) c.D.y = T.y := hg
    choose y hy using fun k => Ideal.Quotient.mk_surjective (g (Ideal.Quotient.mk _ (c.t k)))
    obtain ⟨f, ⟨h1, -, h3⟩, -⟩ := exists_unique_lift c T g (quot_comm c T g hg') y hy
    exact ⟨homOf c T f h1 g h3 hg'⟩
  · have hg : (nlFun γ p X q κ).Pt.map
        (CommRingCat.ofHom (Ideal.quotientMap T.J σ.φ σ.hle)) c.D.y = T.y := σ.pt
    have hs : ∀ k, Ideal.Quotient.mk T.J (σ.φ (c.t k) + y k) =
        Ideal.quotientMap T.J σ.φ σ.hle (Ideal.Quotient.mk _ (c.t k)) := fun k => by
      rw [Ideal.quotientMap_mk, map_add, Ideal.Quotient.eq_zero_iff_mem.2 (hy k), add_zero]
    obtain ⟨f, ⟨h1, h2, h3⟩, hu⟩ := exists_unique_lift c T (Ideal.quotientMap T.J σ.φ σ.hle)
      (quot_comm c T _ hg) (fun k => σ.φ (c.t k) + y k) hs
    refine ⟨homOf c T f h1 _ h3 hg, fun i => ?_, fun τ hτ => hom_ext ?_⟩
    · change f (c.t i) - σ.φ (c.t i) = y i
      rw [h2 i]
      ring
    · obtain ⟨g₀, -, hu₀⟩ := c.rep (CommRingCat.of (T.B ⧸ T.J)) T.y (inU_of_hom c σ)
      have e : Ideal.quotientMap T.J τ.φ τ.hle = Ideal.quotientMap T.J σ.φ σ.hle :=
        (hu₀ _ τ.pt).trans (hu₀ _ σ.pt).symm
      refine hu τ.φ ⟨τ.comm, fun k => ?_, ?_⟩
      · have := hτ k
        rw [← this]
        ring
      · rw [← e]
        rfl

end GlobalTheory.CompanionTheory.ChartMaps
