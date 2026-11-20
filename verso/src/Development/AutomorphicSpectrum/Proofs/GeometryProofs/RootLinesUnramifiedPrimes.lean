import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibrePowerFreePullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowFnsOfAbelianGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerLineBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EtaleSpaceCohomologyEqZeroOfSimplicialRowExact
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankFiniteFlatTorsionSubschemeEqCardPoints

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.HcptTie

section Lattices

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type} [AddCommGroup V]
  [Module Ω V]

/- English proof (translation)
Introduce `p hp`. Take `⟨U, hU, c, hc, hf⟩` from `hL p (hT hp)`. Use `⟨U, hU, c, hc, fun q hq hqU => ?_⟩` and prove the remaining obligations. Establish `h1` using `hf q (hT hq) hqU`. Conclude with `⟨h1.1, (h q hq).trans h1.2⟩`.
-/
theorem flag_congr {L L' : Lat ξ V} {T T' : Set (Cpt ξ)} {r : ℕ} {b : Fin r → V} (hT : T' ⊆ T)
    (h : ∀ q ∈ T', L' q = L q) (hL : L.IsFlagVBOn T b) : L'.IsFlagVBOn T' b := by
  intro p hp
  obtain ⟨U, hU, c, hc, hf⟩ := hL p (hT hp)
  refine ⟨U, hU, c, hc, fun q hq hqU => ?_⟩
  have h1 := hf q (hT hq) hqU
  exact ⟨h1.1, (h q hq).trans h1.2⟩

/- English proof (translation)
Unfold `Lat.gr`. Rewrite using `[h]`.
-/
theorem gr_congr {L L' : Lat ξ V} {q : Cpt ξ} (h : L' q = L q) {r : ℕ} (b : Fin r → V) (i : Fin r) :
    L'.gr b i q = L.gr b i q := by
  unfold Lat.gr
  rw [h]

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hL`.
-/
theorem flag_cast {L : Lat ξ V} {T : Set (Cpt ξ)} {r r' : ℕ} (h : r' = r) {b : Fin r → V}
    (hL : L.IsFlagVBOn T b) : L.IsFlagVBOn T (b ∘ Fin.cast h) := by
  subst h
  exact hL

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem gr_cast (L : Lat ξ V) {r r' : ℕ} (h : r' = r) (b : Fin r → V) (i : Fin r') :
    L.gr (b ∘ Fin.cast h) i = L.gr b (Fin.cast h i) := by
  subst h
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hb`.
-/
theorem ind_cast {r r' : ℕ} (h : r' = r) {b : Fin r → V} {W : Submodule Ω V}
    (hb : LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = W) :
    LinearIndependent Ω (b ∘ Fin.cast h) ∧ Submodule.span Ω (Set.range (b ∘ Fin.cast h)) = W := by
  subst h
  exact hb

/- English proof (translation)
Take `⟨U, hU, b, -, hf⟩` from `h p hp`. Take `⟨hli, hs⟩` from `hf p hp hU`. Use `⟨b 0, hli.ne_zero 0, ?_⟩` and prove the remaining obligations. Rewrite using `[hs, Set.range_unique]`. Both sides reduce to the same expression.
-/
theorem exists_gen {Λ : Lat ξ Ω} {T : Set (Cpt ξ)} (h : Λ.IsVBOn T 1 ⊤) {p : Cpt ξ} (hp : p ∈ T) :
    ∃ s, Λ.IsGenAt p s := by
  obtain ⟨U, hU, b, -, hf⟩ := h p hp
  obtain ⟨hli, hs⟩ := hf p hp hU
  refine ⟨b 0, hli.ne_zero 0, ?_⟩
  rw [hs, Set.range_unique]
  rfl

/- English proof (translation)
Establish `h` using `(GlobalTheory.T.lattice_tensor_power_line_bundle X Ω ξ Unit (fun _ => G) T (fun _ => hG) fun _ => n).2 p hp (fun _ => s) fun _ => hs`. Simplify using `using h`.
-/
theorem tens_gen {G : Lat ξ Ω} {T : Set (Cpt ξ)} (hG : G.IsVBOn T 1 ⊤) (n : ℤ) {p : Cpt ξ} (hp : p ∈ T) {s : Ω}
    (hs : G.IsGenAt p s) : (Lat.tens (fun _ : Unit => G) fun _ => n).IsGenAt p (s ^ n) := by
  have h := (GlobalTheory.T.lattice_tensor_power_line_bundle X Ω ξ Unit (fun _ => G) T (fun _ => hG) fun _ => n).2 p hp (fun _ => s) fun _ => hs
  simpa using h

/- English proof (translation)
Establish `h1 : s⁻¹ ∈ Submodule.span R {w}` using `h ▸ Submodule.mem_span_singleton_self _`. Establish `h2 : w ∈ Submodule.span R {s⁻¹}` using `h ▸ Submodule.mem_span_singleton_self _`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.1 h1`. Take `⟨b, hb⟩` from `Submodule.mem_span_singleton.1 h2`. Establish `ha' : (a : Ω) * w = s⁻¹` using `ha`.

Establish `hb' : (b : Ω) * s⁻¹ = w` using `hb`. Establish `hw : w ≠ 0`. Introduce and unpack `rfl`. Conclude with `inv_ne_zero hs (by simpa using ha'.symm)`. Apply `le_antisymm` to reduce the goal to its premises.

Use `(Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_span_singleton.2 ⟨b, ?_⟩) show (b : Ω) * w⁻¹ = s` and prove the remaining obligations. Establish `hbs : (b : Ω) = w * s`. Rewrite using `[← hb']`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hbs]`.

Clear the denominators using the available nonvanishing facts. Use `(Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_span_singleton.2 ⟨a, ?_⟩) show (a : Ω) * s = w⁻¹` and prove the remaining obligations. Establish `: (a : Ω) = s⁻¹ * w⁻¹`. Rewrite using `[← ha']`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts.
-/
theorem span_inv (R : Subring Ω) {s w : Ω} (hs : s ≠ 0) (h : Submodule.span R {s⁻¹} = Submodule.span R {w}) :
    Submodule.span R {s} = Submodule.span R {w⁻¹} := by
  have h1 : s⁻¹ ∈ Submodule.span R {w} := h ▸ Submodule.mem_span_singleton_self _
  have h2 : w ∈ Submodule.span R {s⁻¹} := h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 h2
  have ha' : (a : Ω) * w = s⁻¹ := ha
  have hb' : (b : Ω) * s⁻¹ = w := hb
  have hw : w ≠ 0 := by
    rintro rfl
    exact inv_ne_zero hs (by simpa using ha'.symm)
  apply le_antisymm
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_span_singleton.2 ⟨b, ?_⟩)
    show (b : Ω) * w⁻¹ = s
    have hbs : (b : Ω) = w * s := by
      rw [← hb']
      field_simp
    rw [hbs]
    field_simp
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_span_singleton.2 ⟨a, ?_⟩)
    show (a : Ω) * s = w⁻¹
    have : (a : Ω) = s⁻¹ * w⁻¹ := by
      rw [← ha']
      field_simp
    rw [this]
    field_simp

variable {K : Type} [Fintype K] {ι : K → Type} {y : (Σ k, ι k) → Ω}

/- English proof (translation)
Use `⟨hd.1, fun q hq c hc => ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `exists_gen hG (Set.mem_univ q)`. Establish `ht` using `tens_gen hG 1 (Set.mem_univ q) hs`. Rewrite using `[h q hq, hs.2, ← hd.2 q (Set.mem_univ q) c hc, ht.2, zpow_one]`.
-/
theorem deg_one {G G' : Lat ξ Ω} {T : Set (Cpt ξ)} {a : K → ℤ} {e : Ω} (hG : G.IsVBOn Set.univ 1 ⊤)
    (hd : (Lat.tens (fun _ : Unit => G) fun _ => (1 : ℤ)).IsDegOn Set.univ y a e) (h : ∀ q ∈ T, G' q = G q) :
    G'.IsDegOn T y a e := by
  refine ⟨hd.1, fun q hq c hc => ?_⟩
  obtain ⟨s, hs⟩ := exists_gen hG (Set.mem_univ q)
  have ht := tens_gen hG 1 (Set.mem_univ q) hs
  rw [h q hq, hs.2, ← hd.2 q (Set.mem_univ q) c hc, ht.2, zpow_one]

/- English proof (translation)
Use `⟨inv_ne_zero hd.1, fun q hq c hc => ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `exists_gen hG (Set.mem_univ q)`. Establish `ht` using `tens_gen hG (-1) (Set.mem_univ q) hs`. Establish `h1` using `hd.2 q (Set.mem_univ q) c hc`. Rewrite `h1` using `[ht.2, zpow_neg_one]`.

Establish `h2` using `span_inv (regAt ξ q) hs.1 h1`. Establish `e1 : (∏ k, y ⟨k, c k⟩ ^ (-a) k) • e⁻¹ = ((∏ k, y ⟨k, c k⟩ ^ a k) • e)⁻¹`. Simplify using `[Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib, mul_inv, mul_comm]`. Rewrite using `[h q hq, hs.2, e1]`. Conclude with `h2`.
-/
theorem deg_neg_one {G G' : Lat ξ Ω} {T : Set (Cpt ξ)} {a : K → ℤ} {e : Ω} (hG : G.IsVBOn Set.univ 1 ⊤)
    (hd : (Lat.tens (fun _ : Unit => G) fun _ => (-1 : ℤ)).IsDegOn Set.univ y a e) (h : ∀ q ∈ T, G' q = G q) :
    G'.IsDegOn T y (-a) e⁻¹ := by
  refine ⟨inv_ne_zero hd.1, fun q hq c hc => ?_⟩
  obtain ⟨s, hs⟩ := exists_gen hG (Set.mem_univ q)
  have ht := tens_gen hG (-1) (Set.mem_univ q) hs
  have h1 := hd.2 q (Set.mem_univ q) c hc
  rw [ht.2, zpow_neg_one] at h1
  have h2 := span_inv (regAt ξ q) hs.1 h1
  have e1 : (∏ k, y ⟨k, c k⟩ ^ (-a) k) • e⁻¹ = ((∏ k, y ⟨k, c k⟩ ^ a k) • e)⁻¹ := by
    simp [Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib, mul_inv, mul_comm]
  rw [h q hq, hs.2, e1]
  exact h2

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hu : IsUnit (p : X.presheaf.stalk q.1)`. Assume the negation of the conclusion as `hnu`. Apply `hne` to reduce the goal to its premises. Establish `h0 : IsLocalRing.residue (X.presheaf.stalk q.1) (p : X.presheaf.stalk q.1) = 0` using `(IsLocalRing.residue_eq_zero_iff _).2 hnu`.

Conclude with `(map_natCast (IsLocalRing.residue (X.presheaf.stalk q.1)) p).symm.trans h0`. Take `⟨u, hu⟩` from `hu`. Establish `e : genMap ξ q (u : X.presheaf.stalk q.1) = (p : Ω)` using `by rw [hu, map_natCast]`. Establish `hm : genMap ξ q ((u⁻¹ : (X.presheaf.stalk q.1)ˣ) : X.presheaf.stalk q.1) * (p : Ω) = 1`. Rewrite using `[← e, ← map_mul, Units.inv_mul, map_one]`.

Use `h ⟨fun h0 => ?_, ⟨_, e⟩, ⟨_, eq_inv_of_mul_eq_one_left hm⟩⟩` and prove the remaining obligations. Rewrite `hm` using `[h0]`. Simplify using `at hm`.
-/
theorem natCast_residue_eq_zero (q : Cpt ξ) {p : ℕ} (h : InFibre ξ p q) : (p : X.residueField q.1) = 0 := by
  by_contra hne
  have hu : IsUnit (p : X.presheaf.stalk q.1) := by
    by_contra hnu
    apply hne
    have h0 : IsLocalRing.residue (X.presheaf.stalk q.1) (p : X.presheaf.stalk q.1) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 hnu
    exact (map_natCast (IsLocalRing.residue (X.presheaf.stalk q.1)) p).symm.trans h0
  obtain ⟨u, hu⟩ := hu
  have e : genMap ξ q (u : X.presheaf.stalk q.1) = (p : Ω) := by rw [hu, map_natCast]
  have hm : genMap ξ q ((u⁻¹ : (X.presheaf.stalk q.1)ˣ) : X.presheaf.stalk q.1) * (p : Ω) = 1 := by
    rw [← e, ← map_mul, Units.inv_mul, map_one]
  refine h ⟨fun h0 => ?_, ⟨_, e⟩, ⟨_, eq_inv_of_mul_eq_one_left hm⟩⟩
  rw [h0] at hm
  simp at hm

end Lattices

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y}

/- English proof (translation)
Establish `hli : LinearIndependent Ω (Fl.b s)`. Use `letI := 𝔐.fn.toAlgebra`. Take `⟨_, _, -, -, -, hli, -⟩` from `Fl.generic`. Conclude with `hli s`. Use `⟨hli, ?_⟩` and prove the remaining obligations.

Set `q0 : Cpt 𝔐.ξ` to `⟨genPt 𝔐.ξ, specializes_rfl⟩`. Take `⟨U, hU, b, hF, hb⟩` from `Fl.sub s q0 (Set.mem_univ _)`. Take `⟨U', hU', b', hs', hb'⟩` from `𝔐.vb s q0 (Set.mem_univ _)`. Establish `e3 : Submodule.span (regAt 𝔐.ξ q0) (Set.range b) = Submodule.span (regAt 𝔐.ξ q0) (Set.range b')` using `(hb q0 (Set.mem_univ _) hU).2.symm.trans (hb' q0 (Set.mem_univ _) hU').2`. Establish `e4 : Submodule.span Ω (Set.range b) = Submodule.span Ω (Set.range b')`.

Rewrite using `[← Submodule.span_span_of_tower (regAt 𝔐.ξ q0) Ω (Set.range b), e3, Submodule.span_span_of_tower]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem flag_basis (Fl : 𝔐.Flag) (s : CMType H ⊕ CMType H) :
    LinearIndependent Ω (Fl.b s) ∧ Submodule.span Ω (Set.range (Fl.b s)) = eigSp 𝔐.ρ (𝔐.emb s) := by
  have hli : LinearIndependent Ω (Fl.b s) := by
    letI := 𝔐.fn.toAlgebra
    obtain ⟨_, _, -, -, -, hli, -⟩ := Fl.generic
    exact hli s
  refine ⟨hli, ?_⟩
  let q0 : Cpt 𝔐.ξ := ⟨genPt 𝔐.ξ, specializes_rfl⟩
  obtain ⟨U, hU, b, hF, hb⟩ := Fl.sub s q0 (Set.mem_univ _)
  obtain ⟨U', hU', b', hs', hb'⟩ := 𝔐.vb s q0 (Set.mem_univ _)
  have e3 : Submodule.span (regAt 𝔐.ξ q0) (Set.range b) = Submodule.span (regAt 𝔐.ξ q0) (Set.range b') :=
    (hb q0 (Set.mem_univ _) hU).2.symm.trans (hb' q0 (Set.mem_univ _) hU').2
  have e4 : Submodule.span Ω (Set.range b) = Submodule.span Ω (Set.range b') := by
    rw [← Submodule.span_span_of_tower (regAt 𝔐.ξ q0) Ω (Set.range b), e3, Submodule.span_span_of_tower]
  calc Submodule.span Ω (Set.range (Fl.b s)) = flagStep Ω (Fl.b s) (labelRk D s) := (FlagGr.step_top _).symm
    _ = flagStep Ω b (labelRk D s) := (hF _).symm
    _ = Submodule.span Ω (Set.range b) := FlagGr.step_top _
    _ = eigSp 𝔐.ρ (𝔐.emb s) := e4.trans hs'

/- English proof (translation)
Use `(Lat.patch_of_not S _ _ fun p' hp' h' => ?_).symm` and prove the remaining obligations. Establish `hne : p ≠ p'` using `fun e => hS (e ▸ hp')`. Conclude with `Lat.not_inFibre_of_coprime q ((Nat.coprime_primes hp (𝔐.S_prime _ hp')).2 hne) hq h'`.
-/
theorem eigLat_eq_V (s : CMType H ⊕ CMType H) {p : ℕ} (hp : p.Prime) (hS : p ∉ S) {q : Cpt 𝔐.ξ}
    (hq : InFibre 𝔐.ξ p q) : 𝔐.M.eigLat 𝔐.ρ (𝔐.emb s) q = 𝔐.V s q := by
  refine (Lat.patch_of_not S _ _ fun p' hp' h' => ?_).symm
  have hne : p ≠ p' := fun e => hS (e ▸ hp')
  exact Lat.not_inFibre_of_coprime q ((Nat.coprime_primes hp (𝔐.S_prime _ hp')).2 hne) hq h'

end Main

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y S _ M 𝔐 Fl e hR p hp hS hd hfib`. Take `⟨hint, -, -, hinj, -, -, -, hreg⟩` from `GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S M.Ω M.K M.ι M.y 𝔐 Subtype.val_injective`. Establish `hcard` using `(LabelCount.labels_injective_card E H l c M.Ω 𝔐.cst).2`. Establish `hnoeth` using `(GlobalTheory.T.regAt_noetherian_model_noetherian 𝔐.X M.Ω 𝔐.ξ ℤ ((k : M.K) → M.ι k) _ 𝔐.tie).2 𝔐.all`. Use `haveI := hnoeth.1`.

Use `haveI := hnoeth.2`. Establish `hpow : PowFns 𝔐.t` using `GlobalTheory.T.powFns_of_abelian_generic E H 𝔐.X 𝔐.t inferInstance inferInstance fun z hz => by`. Establish `h1 : genPt 𝔐.ξ = z` using `hz _ (𝔐.all z)`. Rewrite using `[← h1]`. Conclude with `hint`.

Establish `hc : ∀ τ : CMType H, D.p + D.q - D.p = labelRk D (.inr τ)` using `fun _ => Nat.add_sub_cancel_left _ _`. Set `G : (Σ s, Fin (labelRk D s)) → Lat 𝔐.ξ M.Ω` to `fun x => (𝔐.V x.1).gr (Fl.b x.1) x.2`. Establish `hG : ∀ x, (G x).IsVBOn Set.univ 1 ⊤` using `fun x => (Lat.IsFlagVBOn.isVBOn_gr_inter 𝔐.X M.Ω 𝔐.ξ 𝔐.Li (𝔐.V x.1) Set.univ _ (Fl.b x.1) (flag_basis Fl x.1).1 (Fl.sub x.1)).2.1 x.2`. Establish `hroot : ∀ r, (Lat.tens (fun _ : Unit => G (HodgeCpt.rootIdx D r)) fun _ => HodgeCpt.rootSgn D r).IsDegOn Set.univ M.y (M.xdeg r) (e r)` using `hR`. Establish `hV` using `fun (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ) (hq : InFibre 𝔐.ξ p q) => eigLat_eq_V (𝔐 := 𝔐) s hp hS hq`.

Use `⟨{ X := 𝔐.X ξ := 𝔐.ξ tie := 𝔐.tie t := 𝔐.t pow := hpow fib := fun q hq => (GlobalTheory.T.fibre_power_free_pullback E H Y.X Y.t 𝔐.X 𝔐.t 𝔐.f 𝔐.m q.1).2 (hfib _ ?_) V := 𝔐.Li L := 𝔐.M r := 𝔐.ρ act := 𝔐.act σ := 𝔐.emb σ_inj := hinj card := ?_ conj := fun _ _ => rfl reg := fun q _ s …` and prove the remaining obligations. Establish `h0` using `natCast_residue_eq_zero q hq`. Establish `h1 : ((p : Y.X.residueField (𝔐.f q.1))) = 0`. Apply `(𝔐.f.residueFieldMap q.1).hom.injective` to reduce the goal to its premises. Rewrite using `[map_natCast, map_zero]`.

Conclude with `h0`. Conclude with `h1`. Rewrite `hcard` using `[Fintype.card_sum]`. Use linear arithmetic over natural numbers and integers. Establish `hidx : HodgeCpt.rootIdx D (τ, i) = ⟨.inl τ, ⟨i, h⟩⟩` using `dif_pos h`.

Establish `hsgn : HodgeCpt.rootSgn D (τ, i) = 1` using `if_pos h`. Establish `h1` using `hroot (τ, i)`. Rewrite `h1` using `[hidx, hsgn]`. Conclude with `deg_one (hG _) h1 fun q hq => gr_congr (hV _ q hq) _ _`. Establish `hn : ¬ (i : ℕ) < D.p` using `not_lt.2 hj`.

Establish `hidx : HodgeCpt.rootIdx D (τ, i) = ⟨.inr τ, ⟨D.p + D.q - 1 - i, by have` using `i.2; show _ < D.q; omega⟩⟩ := dif_neg hn`. Establish `hsgn : HodgeCpt.rootSgn D (τ, i) = -1` using `if_neg hn`. Establish `h1` using `hroot (τ, i)`. Rewrite `h1` using `[hidx, hsgn]`. Rewrite using `[gr_cast]`.

Conclude with `deg_neg_one (hG _) h1 fun q hq => gr_congr (hV _ q hq) _ _`.
-/
theorem drTie_of_hodgeCpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω), Fl.RootLines M.xdeg e → ∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ NumberField.discr E → (∀ z : Y.X, (p : Y.X.residueField z) = 0 → FibPF Y.t z) → Nonempty (DRTie M D.p p H) := by
  intro E _ _ _ H D l Xo c Y S _ M 𝔐 Fl e hR p hp hS hd hfib
  obtain ⟨hint, -, -, hinj, -, -, -, hreg⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S M.Ω M.K M.ι
    M.y 𝔐 Subtype.val_injective
  have hcard := (LabelCount.labels_injective_card E H l c M.Ω 𝔐.cst).2
  have hnoeth := (GlobalTheory.T.regAt_noetherian_model_noetherian 𝔐.X M.Ω 𝔐.ξ ℤ ((k : M.K) → M.ι k) _ 𝔐.tie).2 𝔐.all
  haveI := hnoeth.1
  haveI := hnoeth.2
  have hpow : PowFns 𝔐.t := GlobalTheory.T.powFns_of_abelian_generic E H 𝔐.X 𝔐.t inferInstance inferInstance fun z hz => by
    have h1 : genPt 𝔐.ξ = z := hz _ (𝔐.all z)
    rw [← h1]
    exact hint
  have hc : ∀ τ : CMType H, D.p + D.q - D.p = labelRk D (.inr τ) := fun _ => Nat.add_sub_cancel_left _ _
  let G : (Σ s, Fin (labelRk D s)) → Lat 𝔐.ξ M.Ω := fun x => (𝔐.V x.1).gr (Fl.b x.1) x.2
  have hG : ∀ x, (G x).IsVBOn Set.univ 1 ⊤ := fun x =>
    (Lat.IsFlagVBOn.isVBOn_gr_inter 𝔐.X M.Ω 𝔐.ξ 𝔐.Li (𝔐.V x.1) Set.univ _ (Fl.b x.1) (flag_basis Fl x.1).1
      (Fl.sub x.1)).2.1 x.2
  have hroot : ∀ r, (Lat.tens (fun _ : Unit => G (HodgeCpt.rootIdx D r)) fun _ => HodgeCpt.rootSgn D r).IsDegOn Set.univ
      M.y (M.xdeg r) (e r) := hR
  have hV := fun (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ) (hq : InFibre 𝔐.ξ p q) =>
    eigLat_eq_V (𝔐 := 𝔐) s hp hS hq
  refine ⟨{
    X := 𝔐.X
    ξ := 𝔐.ξ
    tie := 𝔐.tie
    t := 𝔐.t
    pow := hpow
    fib := fun q hq => (GlobalTheory.T.fibre_power_free_pullback E H Y.X Y.t 𝔐.X 𝔐.t 𝔐.f 𝔐.m q.1).2 (hfib _ ?_)
    V := 𝔐.Li
    L := 𝔐.M
    r := 𝔐.ρ
    act := 𝔐.act
    σ := 𝔐.emb
    σ_inj := hinj
    card := ?_
    conj := fun _ _ => rfl
    reg := fun q _ s a => hreg s a q
    unram := hd
    b₁ := fun τ => Fl.b (.inl τ)
    b₂ := fun τ => Fl.b (.inr τ) ∘ Fin.cast (hc τ)
    ind₁ := fun τ => flag_basis Fl (.inl τ)
    ind₂ := fun τ => ind_cast (hc τ) (flag_basis Fl (.inr τ))
    flag₁ := fun τ => flag_congr (Set.subset_univ _) (fun q hq => hV _ q hq) (Fl.sub (.inl τ))
    flag₂ := fun τ => flag_cast (hc τ) (flag_congr (Set.subset_univ _) (fun q hq => hV _ q hq) (Fl.sub (.inr τ)))
    deg₁ := fun τ i h => ⟨e (τ, i), ?_⟩
    deg₂ := fun τ i h hj => ⟨(e (τ, i))⁻¹, ?_⟩ }⟩
  · have h0 := natCast_residue_eq_zero q hq
    have h1 : ((p : Y.X.residueField (𝔐.f q.1))) = 0 := by
      apply (𝔐.f.residueFieldMap q.1).hom.injective
      rw [map_natCast, map_zero]
      exact h0
    exact h1
  · rw [Fintype.card_sum] at hcard
    omega
  · have hidx : HodgeCpt.rootIdx D (τ, i) = ⟨.inl τ, ⟨i, h⟩⟩ := dif_pos h
    have hsgn : HodgeCpt.rootSgn D (τ, i) = 1 := if_pos h
    have h1 := hroot (τ, i)
    rw [hidx, hsgn] at h1
    exact deg_one (hG _) h1 fun q hq => gr_congr (hV _ q hq) _ _
  · have hn : ¬ (i : ℕ) < D.p := not_lt.2 hj
    have hidx : HodgeCpt.rootIdx D (τ, i) = ⟨.inr τ, ⟨D.p + D.q - 1 - i, by have := i.2; show _ < D.q; omega⟩⟩ := dif_neg hn
    have hsgn : HodgeCpt.rootSgn D (τ, i) = -1 := if_neg hn
    have h1 := hroot (τ, i)
    rw [hidx, hsgn] at h1
    rw [gr_cast]
    exact deg_neg_one (hG _) h1 fun q hq => gr_congr (hV _ q hq) _ _

end GlobalTheory.CompanionTheory.Ar.Conj.HcptTie
