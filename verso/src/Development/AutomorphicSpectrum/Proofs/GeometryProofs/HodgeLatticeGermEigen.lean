import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransportStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame

section Abstract

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {E : Type} [Field E] [NumberField E]
  {A : Subring K}

/- English proof (translation)
Establish `e : t i = ρ 1 (t i)` using `by simp`. Rewrite using `[h.2.2, e, ← (RingOfIntegers.basis E).sum_repr 1, map_sum, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, LinearMap.smul_apply]`. Conclude with `zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(i, k), rfl⟩)) _`.
-/
theorem mem_of_isFreeOn {ρ : 𝓞 E →+* Module.End K V} {L : Submodule A V} {N : ℕ} {t : Fin N → V}
    (h : HT.IsFreeOn ρ L t) (i : Fin N) : t i ∈ L := by
  have e : t i = ρ 1 (t i) := by simp
  rw [h.2.2, e, ← (RingOfIntegers.basis E).sum_repr 1, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_zsmul, LinearMap.smul_apply]
  exact zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(i, k), rfl⟩)) _

/- English proof (translation)
Use `choose x hx using fun i => (hrange (t i)).1 (mem_of_isFreeOn h i)`. Establish `hΦ : ∀ c : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → R, Φ (∑ q, c q • rB (RingOfIntegers.basis E q.2) (x q.1)) = ∑ q, f (c q) • ρ (RingOfIntegers.basis E q.2) (t q.1)` using `fun c => by`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun q _ => by rw [hsmul, hact, hx]`. Use `⟨x, hx, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc q`. Establish `h1` using `Fintype.linearIndependent_iff.1 h.1 (fun q => f (c q)) (by rw [← hΦ, hc, map_zero])`. Conclude with `hf ((h1 q).trans (map_zero f).symm)`. Rewrite using `[eq_top_iff]`.

Introduce and unpack `y -`. Establish `hy : Φ y ∈ L` using `(hrange _).2 ⟨y, rfl⟩`. Rewrite `hy` using `[h.2.2]`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun A).1 hy`. Use `choose c' hc' using fun q => (hA (c q : K)).1 (c q).2`.

Establish `e : y = ∑ q, c' q • rB (RingOfIntegers.basis E q.2) (x q.1)` using `hinj (by`. Rewrite using `[hΦ, ← hc]`. Conclude with `Finset.sum_congr rfl fun q _ => by rw [hc']; rfl)`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)`.
-/
theorem exists_lift_basis {R Y : Type} [CommRing R] [AddCommGroup Y] [Module R Y] (f : R →+* K)
    (hf : Function.Injective f) (hA : ∀ a, a ∈ A ↔ ∃ c, f c = a) (Φ : Y →+ V)
    (hsmul : ∀ (c : R) y, Φ (c • y) = f c • Φ y) (hinj : Function.Injective Φ)
    {ρ : 𝓞 E →+* Module.End K V} {L : Submodule A V} (hrange : ∀ v, v ∈ L ↔ ∃ y, Φ y = v)
    (rB : 𝓞 E → Y → Y) (hact : ∀ a y, Φ (rB a y) = ρ a (Φ y)) {N : ℕ} {t : Fin N → V}
    (h : HT.IsFreeOn ρ L t) :
    ∃ x : Fin N → Y, (∀ j, Φ (x j) = t j) ∧
      LinearIndependent R (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        rB (RingOfIntegers.basis E q.2) (x q.1)) ∧
      Submodule.span R (Set.range fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        rB (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ := by
  choose x hx using fun i => (hrange (t i)).1 (mem_of_isFreeOn h i)
  have hΦ : ∀ c : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → R,
      Φ (∑ q, c q • rB (RingOfIntegers.basis E q.2) (x q.1)) =
        ∑ q, f (c q) • ρ (RingOfIntegers.basis E q.2) (t q.1) := fun c => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [hsmul, hact, hx]
  refine ⟨x, hx, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc q
    have h1 := Fintype.linearIndependent_iff.1 h.1 (fun q => f (c q)) (by rw [← hΦ, hc, map_zero])
    exact hf ((h1 q).trans (map_zero f).symm)
  · rw [eq_top_iff]
    rintro y -
    have hy : Φ y ∈ L := (hrange _).2 ⟨y, rfl⟩
    rw [h.2.2] at hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hy
    choose c' hc' using fun q => (hA (c q : K)).1 (c q).2
    have e : y = ∑ q, c' q • rB (RingOfIntegers.basis E q.2) (x q.1) := hinj (by
      rw [hΦ, ← hc]
      exact Finset.sum_congr rfl fun q _ => by rw [hc']; rfl)
    rw [e]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)

end Abstract

/- English proof (translation)
Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem w hw => exact hw`. Consider the case `zero => exact ⟨0, fun i => ⟨A.zero_mem, A.zero_mem⟩, (map_zero T).symm⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨y, hy, rfl⟩` from `ha`.

Take `⟨z, hz, rfl⟩` from `hb`. Conclude with `⟨y + z, fun i => ⟨A.add_mem (hy i).1 (hz i).1, A.add_mem (hy i).2 (hz i).2⟩, (map_add T y z).symm⟩`. Consider the case `smul c a _ ha`. Take `⟨y, hy, rfl⟩` from `ha`. Conclude with `⟨(c : Ω) • y, fun i => ⟨A.mul_mem c.2 (hy i).1, A.mul_mem c.2 (hy i).2⟩, (map_smul T (c : Ω) y).symm⟩`.
-/
theorem exists_of_mem_stdLat {Ω : Type} [Field Ω] {A : Subring Ω} {d : ℕ}
    {T : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω)} {w : (Fin d → Ω) × (Fin d → Ω)}
    (h : w ∈ stdLat A T) : ∃ y₀ : (Fin d → Ω) × (Fin d → Ω), (∀ i, y₀.1 i ∈ A ∧ y₀.2 i ∈ A) ∧ w = T y₀ := by
  induction h using Submodule.span_induction with
  | mem w hw => exact hw
  | zero => exact ⟨0, fun i => ⟨A.zero_mem, A.zero_mem⟩, (map_zero T).symm⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, hy, rfl⟩ := ha
    obtain ⟨z, hz, rfl⟩ := hb
    exact ⟨y + z, fun i => ⟨A.add_mem (hy i).1 (hz i).1, A.add_mem (hy i).2 (hz i).2⟩, (map_add T y z).symm⟩
  | smul c a _ ha =>
    obtain ⟨y, hy, rfl⟩ := ha
    exact ⟨(c : Ω) • y, fun i => ⟨A.mul_mem c.2 (hy i).1, A.mul_mem c.2 (hy i).2⟩, (map_smul T (c : Ω) y).symm⟩

/- English proof (translation)
Introduce `y y' h`. Establish `h1` using `congrArg Prod.fst h`. Establish `h2` using `congrArg Prod.snd h`. Conclude with `Prod.ext h1 ((dotProductEquiv Ω (Fin d)).injective h2)`.
-/
theorem toVec_injective (Ω : Type) [Field Ω] (d : ℕ) : Function.Injective (toVec Ω d) := by
  intro y y' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext h1 ((dotProductEquiv Ω (Fin d)).injective h2)

/- English proof (translation)
Introduce and unpack `⟨a, φ⟩`. Take `⟨b, rfl⟩` from `(dotProductEquiv Ω (Fin d)).surjective φ`. Conclude with `⟨(a, b), rfl⟩`.
-/
theorem toVec_surjective (Ω : Type) [Field Ω] (d : ℕ) : Function.Surjective (toVec Ω d) := by
  rintro ⟨a, φ⟩
  obtain ⟨b, rfl⟩ := (dotProductEquiv Ω (Fin d)).surjective φ
  exact ⟨(a, b), rfl⟩

section Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} [StarRing (𝓞 E)]
  {Ω : Type} [Field Ω] {t : SAB H X} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {d r : ℕ}
  {M : LieModel t.G ξ (Fin d → Ω)} {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)}

/- English proof (translation)
Introduce `_ _ h` and use `Prod.ext (funext fun i => hf (congrFun (congrArg Prod.fst h) i)) (funext fun i => hf (congrFun (congrArg Prod.snd h) i))`.
-/
theorem vmap_injective {R S : Type} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (vmap (d := d) f) := fun _ _ h =>
  Prod.ext (funext fun i => hf (congrFun (congrArg Prod.fst h) i))
    (funext fun i => hf (congrFun (congrArg Prod.snd h) i))

/- English proof (translation)
Introduce `_ _ h` and use `vmap_injective (hξ.inj p) ((GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (S.iso p)).2.2.1.1 (toVec_injective Ω d h))`.
-/
theorem toH_injective (hξ : IsCptGen ξ) (S : GermSys t ξ M) (p : Cpt ξ) : Function.Injective (toH S p) :=
  fun _ _ h => vmap_injective (hξ.inj p)
    ((GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (S.iso p)).2.2.1.1 (toVec_injective Ω d h))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Take `⟨w, rfl⟩` from `toVec_surjective Ω d v`. Take `⟨y₀, hy₀, rfl⟩` from `exists_of_mem_stdLat ((hG.2 p w).1 hv)`. Use `choose a ha using fun i => (hy₀ i).1`.

Use `choose b hb using fun i => (hy₀ i).2`. Use `⟨(a, b), ?_⟩` and prove the remaining obligations. Establish `e : vmap (genMap ξ p) (a, b) = y₀` using `Prod.ext (funext ha) (funext hb)`. Rewrite using `[toH, e]`. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `(hG.2 p _).2 (Submodule.subset_span ⟨vmap (genMap ξ p) y, fun i => ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, rfl⟩)`.
-/
theorem toH_mem_iff (S : GermSys t ξ M) {𝓗 : HodgeLat M.lat ρ H.bar r} (hG : S.Gives 𝓗) (p : Cpt ξ)
    (v : (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)) : v ∈ 𝓗.HL p ↔ ∃ y, toH S p y = v := by
  constructor
  · intro hv
    obtain ⟨w, rfl⟩ := toVec_surjective Ω d v
    obtain ⟨y₀, hy₀, rfl⟩ := exists_of_mem_stdLat ((hG.2 p w).1 hv)
    choose a ha using fun i => (hy₀ i).1
    choose b hb using fun i => (hy₀ i).2
    refine ⟨(a, b), ?_⟩
    have e : vmap (genMap ξ p) (a, b) = y₀ := Prod.ext (funext ha) (funext hb)
    rw [toH, e]
  · rintro ⟨y, rfl⟩
    exact (hG.2 p _).2 (Submodule.subset_span ⟨vmap (genMap ξ p) y,
      fun i => ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, rfl⟩)

/- English proof (translation)
Establish `h1` using `vmap_rhoH (S.mapK p) a y`. Establish `h2` using `LinearMap.congr_fun ((GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (S.iso p)).2.2.2.2.1 a) (vmap (genMap ξ p) y)`. Establish `h3` using `hG.1 a (transH (S.φ p) (S.ψ p) (S.lam p) (vmap (genMap ξ p) y))`. Establish `e1` using `congrArg (fun z => toVec Ω d (transH (S.φ p) (S.ψ p) (S.lam p) z)) h1`. Establish `e2` using `congrArg (toVec Ω d) h2.symm`.

Conclude with `(e1.trans e2).trans h3.symm`.
-/
theorem toH_rhoH (S : GermSys t ξ M) {𝓗 : HodgeLat M.lat ρ H.bar r} (hG : S.Gives 𝓗) (p : Cpt ξ) (a : 𝓞 E)
    (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (rhoH (S.g p).B a y) = 𝓗.ρH a (toH S p y) := by
  have h1 := vmap_rhoH (S.mapK p) a y
  have h2 := LinearMap.congr_fun ((GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (S.iso p)).2.2.2.2.1 a) (vmap (genMap ξ p) y)
  have h3 := hG.1 a (transH (S.φ p) (S.ψ p) (S.lam p) (vmap (genMap ξ p) y))
  have e1 := congrArg (fun z => toVec Ω d (transH (S.φ p) (S.ψ p) (S.lam p) z)) h1
  have e2 := congrArg (toVec Ω d) h2.symm
  exact (e1.trans e2).trans h3.symm

end Germ

/- English proof (translation)
Introduce `E _ _ _ H _ X t Ω _ _ ξ d r M S ρ 𝓗 σ u hξ hG hσ _ hu p`. Take `⟨U, hU, x, hx⟩` from `𝓗.free p`. Establish `hfree` using `hx p hU`. Take `⟨x', h1, h2, h3⟩` from `exists_lift_basis (genMap ξ p) (hξ.inj p) (A := regAt ξ p) (fun _ => Iff.rfl) (AddMonoidHom.mk' (toH S p) (toH_add S p)) (toH_smul S p) (toH_injective hξ S p) (toH_mem_iff S hG p) (fun a y => rhoH (S.g p).B a y) (toH_rhoH S hG p) hfree`. Establish `hA : ∀ i, ∃ c : Fin r → Ω, ∑ l, c l • u l = HT.eigProj 𝓗.ρH σ (x i)` using `fun i => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hu ▸ HT.LatBasic.eigProj_mem _ _ _)`.

Use `choose A hA using hA`. Use `⟨x', Matrix.of A, ⟨h2, h3⟩, ?_, fun j => ?_⟩` and prove the remaining obligations. Establish `e : (fun j => ∑ l, Matrix.of A j l • u l) = fun j => HT.eigProj 𝓗.ρH σ (x j)` using `funext hA`. Rewrite using `[e]`. Conclude with `⟨HodgeDeterminantLattice.linearIndependent_eigProj σ hfree, HodgeDeterminantLattice.eigQuot_eq_span σ hfree fun a => ⟨⟨_, hσ p a⟩, rfl⟩⟩`.

Use `h1 j` as an intermediate fact. Express the relevant statement in the definitionally equal form `toH S p (x' j) = x j at this`. Rewrite using `[this]`. Conclude with `(hA j).symm`.
-/
theorem exists_basis_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)) (𝓗 : HodgeLat M.lat ρ H.bar r) (σ : E →+* Ω) (u : Fin r → (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)), IsCptGen ξ → S.Gives 𝓗 → (∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) → LinearIndependent Ω u → Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → ∀ p : Cpt ξ, ∃ (x : Fin r → (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) (A : Matrix (Fin r) (Fin r) Ω), IsHBasis (S.g p).B x ∧ (𝓗.quot σ).IsFrameAt (fun j => ∑ l, A j l • u l) p ∧ ∀ j, HT.eigProj 𝓗.ρH σ (toH S p (x j)) = ∑ l, A j l • u l := by
  intro E _ _ _ H _ X t Ω _ _ ξ d r M S ρ 𝓗 σ u hξ hG hσ _ hu p
  obtain ⟨U, hU, x, hx⟩ := 𝓗.free p
  have hfree := hx p hU
  obtain ⟨x', h1, h2, h3⟩ := exists_lift_basis (genMap ξ p) (hξ.inj p) (A := regAt ξ p) (fun _ => Iff.rfl)
    (AddMonoidHom.mk' (toH S p) (toH_add S p)) (toH_smul S p) (toH_injective hξ S p)
    (toH_mem_iff S hG p) (fun a y => rhoH (S.g p).B a y) (toH_rhoH S hG p) hfree
  have hA : ∀ i, ∃ c : Fin r → Ω, ∑ l, c l • u l = HT.eigProj 𝓗.ρH σ (x i) := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (hu ▸ HT.LatBasic.eigProj_mem _ _ _)
  choose A hA using hA
  refine ⟨x', Matrix.of A, ⟨h2, h3⟩, ?_, fun j => ?_⟩
  · have e : (fun j => ∑ l, Matrix.of A j l • u l) = fun j => HT.eigProj 𝓗.ρH σ (x j) := funext hA
    rw [e]
    exact ⟨HodgeDeterminantLattice.linearIndependent_eigProj σ hfree,
      HodgeDeterminantLattice.eigQuot_eq_span σ hfree fun a => ⟨⟨_, hσ p a⟩, rfl⟩⟩
  · have := h1 j
    change toH S p (x' j) = x j at this
    rw [this]
    exact (hA j).symm

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame
