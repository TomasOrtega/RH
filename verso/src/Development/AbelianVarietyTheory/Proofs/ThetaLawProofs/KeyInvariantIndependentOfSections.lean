import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAfterDvrExtension
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAfterDvrExtensionStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantEqOfIndependentGenericTuplesStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAlgClosedTransversalStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GenericSectionsMeetTransversallyStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantFromIntersectionUniqueStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsAlgHomOfIsTranscendenceBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KaIndep

/- English proof (translation)
Use `⟨⟨fun i => ∑ k, cst x.P.A.hom ((pw x.P.L (l : ℤ)).U i) (c k) * (b k).f i, ?_⟩, fun i => rfl⟩` and prove the remaining obligations. Introduce `i j`. Establish `e4 : ∀ (V W : x.P.A.left.Opens) (h : W ≤ V) (a : R), (x.P.A.left.presheaf.map (homOfLE h).op).hom (cst x.P.A.hom V a) = cst x.P.A.hom W a`. Introduce `V W h a`. Simplify using `only [AbLaw.cst, RingHom.comp_apply]`.

Conclude with `GlobalTheory.KeyVia.res_appLE (φ := x.P.A.hom) (U := ⊤) _ h _`. Simplify using `only [map_sum, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `e3` using `(b k).compat i j`. Rewrite using `[e4, e4, e3]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_coords {R : Type} [CommRing R] (x : KeyIn R) {l N : ℕ} (b : Fin N → RR x l) (c : Fin N → R) :
    ∃ s : RR x l, Coords x b c s.f := by
  refine ⟨⟨fun i => ∑ k, cst x.P.A.hom ((pw x.P.L (l : ℤ)).U i) (c k) * (b k).f i, ?_⟩, fun i => rfl⟩
  intro i j
  have e4 : ∀ (V W : x.P.A.left.Opens) (h : W ≤ V) (a : R),
      (x.P.A.left.presheaf.map (homOfLE h).op).hom (cst x.P.A.hom V a) = cst x.P.A.hom W a := by
    intro V W h a
    simp only [AbLaw.cst, RingHom.comp_apply]
    exact GlobalTheory.KeyVia.res_appLE (φ := x.P.A.hom) (U := ⊤) _ h _
  simp only [map_sum, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e3 := (b k).compat i j
  rw [e4, e4, e3]
  ring

/- English proof (translation)
Establish `hf : s.f = t.f` using `funext fun i => (hs i).trans (ht i).symm`. Consider the cases of `s`. Consider the cases of `t`. Consider the cases of `hf`. Both sides reduce to the same expression.
-/
theorem eq_of_coords {R : Type} [CommRing R] {x : KeyIn R} {l N : ℕ} {b : Fin N → RR x l} {c : Fin N → R}
    {s t : RR x l} (hs : Coords x b c s.f) (ht : Coords x b c t.f) : s = t := by
  have hf : s.f = t.f := funext fun i => (hs i).trans (ht i).symm
  cases s
  cases t
  cases hf
  rfl

/- English proof (translation)
Take `⟨-, hl, hl', -⟩` from `h`. Unfold `degProd`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `j hj`. Establish `hj' : j ≤ g` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)`.

Establish `hjn : j * n ≤ g * n` using `Nat.mul_le_mul_right n hj'`. Apply the tactic sequence `apply mul_ne_zero <;> omega`.
-/
theorem degProd_ne_zero {g n l l' : ℕ} {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ} (h : admitted g n l l' al) :
    degProd g n l l' ≠ 0 := by
  obtain ⟨-, hl, hl', -⟩ := h
  unfold degProd
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  have hj' : j ≤ g := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hjn : j * n ≤ g * n := Nat.mul_le_mul_right n hj'
  apply mul_ne_zero <;> omega

variable {K : Type} [Field K] {x : KeyIn K} {n : ℕ}

def Framed (b : Fin (n ^ x.P.g) → RR x n) {R : Type} [CommRing R] (f : K →+* R)
    (T : Fin x.P.g × Fin (n ^ x.P.g) → R) (x' : KeyIn R) (s : Fin x'.P.g → RR x' n) : Prop :=
  ∃ φ w, ∃ (hg : x'.P.g = x.P.g) (b' : Fin (n ^ x.P.g) → RR x' n), KeyVia x' x f φ w ∧
    (∀ k, SecVia x' x φ w (b' k) (b k)) ∧ ∀ i, Coords x' b' (fun k => T (i.cast hg, k)) (s i).f

variable {b : Fin (n ^ x.P.g) → RR x n}

/- English proof (translation)
Take `⟨x', hx'⟩` from `GlobalTheory.KeyPow.exists_keyPB_ring x f`. Take `⟨φ, w, H⟩` from `(GlobalTheory.KeyVia.main K R x x' f).1.1 hx'`. Take `⟨_, hg, _⟩` from `id H`. Establish `M` using `(GlobalTheory.KeyVia.main K R x x' f).2 φ w H`. Use `choose b' hb' _ using fun k => M.1 n (b k)`.

Use `choose s hs using fun i : Fin x'.P.g => exists_coords x' b' (fun k => T (i.cast hg, k))`. Conclude with `⟨x', s, φ, w, hg, b', H, hb', hs⟩`.
-/
theorem exists_framed (b : Fin (n ^ x.P.g) → RR x n) {R : Type} [CommRing R] (f : K →+* R)
    (T : Fin x.P.g × Fin (n ^ x.P.g) → R) : ∃ x' s, Framed b f T x' s := by
  obtain ⟨x', hx'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring x f
  obtain ⟨φ, w, H⟩ := (GlobalTheory.KeyVia.main K R x x' f).1.1 hx'
  obtain ⟨_, hg, _⟩ := id H
  have M := (GlobalTheory.KeyVia.main K R x x' f).2 φ w H
  choose b' hb' _ using fun k => M.1 n (b k)
  choose s hs using fun i : Fin x'.P.g => exists_coords x' b' (fun k => T (i.cast hg, k))
  exact ⟨x', s, φ, w, hg, b', H, hb', hs⟩

/- English proof (translation)
Take `⟨_, _, hg, _⟩` from `h`. Conclude with `hg`.
-/
theorem Framed.g_eq {R : Type} [CommRing R] {f : K →+* R} {T : Fin x.P.g × Fin (n ^ x.P.g) → R} {x' : KeyIn R}
    {s : Fin x'.P.g → RR x' n} (h : Framed b f T x' s) : x'.P.g = x.P.g := by
  obtain ⟨_, _, hg, _⟩ := h
  exact hg

/- English proof (translation)
Take `⟨φ1, w1, hg1, b1, H1, hb1, hs1⟩` from `h`. Take `⟨φ2, w2, hg2, b2, H2, hb2, hs2⟩` from `h'`. Take `⟨φ, w, H, -, hsec⟩` from `GlobalTheory.KaLift.keyVia_cancel H1 H2`. Establish `hg : x''.P.g = x'.P.g` using `hg2.trans hg1.symm`. Use `⟨φ, w, hg, H, fun i => ?_⟩` and prove the remaining obligations.

Establish `hb : ∀ k, SecVia x'' x' φ w (b2 k) (b1 k)` using `fun k => hsec n (b k) (b1 k) (b2 k) (hb1 k) (hb2 k)`. Establish `M` using `(GlobalTheory.KeyVia.main R R' x' x'' j).2 φ w H`. Take `⟨t, ht, -⟩` from `M.1 n (s (i.cast hg))`. Establish `hc` using `M.2.2 n (n ^ x.P.g) b1 b2 (s (i.cast hg)) t (fun k => T ((i.cast hg).cast hg1, k)) hb ht (hs1 _)`. Establish `e : (i.cast hg).cast hg1 = i.cast hg2` using `Fin.ext rfl`.

Rewrite `hc` using `[e]`. Establish `ht' : t = s' i` using `eq_of_coords hc (hs2 i)`. Rewrite using `[← ht']`. Conclude with `ht`.
-/
theorem Framed.via {R R' : Type} [CommRing R] [CommRing R'] {f : K →+* R} {j : R →+* R'}
    {T : Fin x.P.g × Fin (n ^ x.P.g) → R} {x' : KeyIn R} {s : Fin x'.P.g → RR x' n} {x'' : KeyIn R'}
    {s' : Fin x''.P.g → RR x'' n} (h : Framed b f T x' s) (h' : Framed b (j.comp f) (j ∘ T) x'' s') :
    ∃ φ w, ∃ hg : x''.P.g = x'.P.g, KeyVia x'' x' j φ w ∧ ∀ i, SecVia x'' x' φ w (s' i) (s (i.cast hg)) := by
  obtain ⟨φ1, w1, hg1, b1, H1, hb1, hs1⟩ := h
  obtain ⟨φ2, w2, hg2, b2, H2, hb2, hs2⟩ := h'
  obtain ⟨φ, w, H, -, hsec⟩ := GlobalTheory.KaLift.keyVia_cancel H1 H2
  have hg : x''.P.g = x'.P.g := hg2.trans hg1.symm
  refine ⟨φ, w, hg, H, fun i => ?_⟩
  have hb : ∀ k, SecVia x'' x' φ w (b2 k) (b1 k) := fun k => hsec n (b k) (b1 k) (b2 k) (hb1 k) (hb2 k)
  have M := (GlobalTheory.KeyVia.main R R' x' x'' j).2 φ w H
  obtain ⟨t, ht, -⟩ := M.1 n (s (i.cast hg))
  have hc := M.2.2 n (n ^ x.P.g) b1 b2 (s (i.cast hg)) t (fun k => T ((i.cast hg).cast hg1, k)) hb ht (hs1 _)
  have e : (i.cast hg).cast hg1 = i.cast hg2 := Fin.ext rfl
  rw [e] at hc
  have ht' : t = s' i := eq_of_coords hc (hs2 i)
  rw [← ht']
  exact ht

variable {l l' : ℕ} {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ}

/- English proof (translation)
Take `⟨φ, w, hg, H, hs⟩` from `h.via h'`. Establish `hA' : admitted x'.P.g n l l' al` using `by rw [h.g_eq]; exact hA`. Conclude with `GlobalTheory.T.keyInvariant_baseChange hL R R' x' x'' j φ w n l l' al hg s s' κ hA' H hs hκ`.
-/
theorem Framed.kaVal (hL : Out.Laws) (hA : admitted x.P.g n l l' al) {R R' : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing R'] [IsLocalRing R'] {f : K →+* R} {j : R →+* R'}
    {T : Fin x.P.g × Fin (n ^ x.P.g) → R} {x' : KeyIn R} {s : Fin x'.P.g → RR x' n} {x'' : KeyIn R'}
    {s' : Fin x''.P.g → RR x'' n} (h : Framed b f T x' s) (h' : Framed b (j.comp f) (j ∘ T) x'' s') {κ : Rˣ}
    (hκ : KaVal x' n l l' al s κ) : KaVal x'' n l l' al s' (Units.map j.toMonoidHom κ) := by
  obtain ⟨φ, w, hg, H, hs⟩ := h.via h'
  have hA' : admitted x'.P.g n l l' al := by rw [h.g_eq]; exact hA
  exact GlobalTheory.T.keyInvariant_baseChange hL R R' x' x'' j φ w n l l' al hg s s' κ hA' H hs hκ

def ValAt (b : Fin (n ^ x.P.g) → RR x n) (l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (R : Type) [CommRing R]
    [Algebra K R] (T : Fin x.P.g × Fin (n ^ x.P.g) → R) (a : R) : Prop :=
  ∃ x' s, ∃ κ : Rˣ, Framed b (algebraMap K R) T x' s ∧ KaVal x' n l l' al s κ ∧ a = κ

/- English proof (translation)
Take `⟨x', s, κ, hf, hκ, rfl⟩` from `h`. Take `⟨x'', s'', hf''⟩` from `exists_framed b (algebraMap K R') (j ∘ T)`. Establish `e : (j : R →+* R').comp (algebraMap K R) = algebraMap K R'` using `j.comp_algebraMap`. Establish `hf2 : Framed b ((j : R →+* R').comp (algebraMap K R)) ((j : R →+* R') ∘ T) x'' s''`. Rewrite using `[e]`.

Conclude with `hf''`. Conclude with `⟨x'', s'', _, hf'', hf.kaVal hL hA hf2 hκ, rfl⟩`.
-/
theorem valAt_map (hL : Out.Laws) (hA : admitted x.P.g n l l' al) (R R' : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing R'] [IsLocalRing R'] [Algebra K R] [Algebra K R'] (j : R →ₐ[K] R')
    (T : Fin x.P.g × Fin (n ^ x.P.g) → R) (a : R) (h : ValAt b l l' al R T a) : ValAt b l l' al R' (j ∘ T) (j a) := by
  obtain ⟨x', s, κ, hf, hκ, rfl⟩ := h
  obtain ⟨x'', s'', hf''⟩ := exists_framed b (algebraMap K R') (j ∘ T)
  have e : (j : R →+* R').comp (algebraMap K R) = algebraMap K R' := j.comp_algebraMap
  have hf2 : Framed b ((j : R →+* R').comp (algebraMap K R)) ((j : R →+* R') ∘ T) x'' s'' := by
    rw [e]; exact hf''
  exact ⟨x'', s'', _, hf'', hf.kaVal hL hA hf2 hκ, rfl⟩

/- English proof (translation)
Take `⟨x1, s1, κ1, h1, hk1, rfl⟩` from `h`. Take `⟨x2, s2, κ2, h2, hk2, rfl⟩` from `h'`. Establish `: CharZero F` using `charZero_of_injective_algebraMap (algebraMap K F).injective`. Establish `h2' : Framed b ((RingHom.id F).comp (algebraMap K F)) (RingHom.id F ∘ T) x2 s2`. Simplify `h2` using `only [RingHom.id_comp, RingHom.coe_id, Function.id_comp]`.

Establish `hk` using `h1.kaVal hL hA h2' hk1`. Establish `hA2 : admitted x2.P.g n l l' al` using `by rw [h2.g_eq]; exact hA`. Establish `e` using `GlobalTheory.T.keyInvariantFromIntersection_unique hL F x2 n l l' al s2 _ _ hA2 hk hk2`. Rewrite using `[← e]`. Both sides reduce to the same expression.
-/
theorem valAt_unique [CharZero K] (hL : Out.Laws) (hA : admitted x.P.g n l l' al) (F : Type) [Field F] [Algebra K F]
    (T : Fin x.P.g × Fin (n ^ x.P.g) → F) (a a' : F) (h : ValAt b l l' al F T a) (h' : ValAt b l l' al F T a') :
    a = a' := by
  obtain ⟨x1, s1, κ1, h1, hk1, rfl⟩ := h
  obtain ⟨x2, s2, κ2, h2, hk2, rfl⟩ := h'
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have h2' : Framed b ((RingHom.id F).comp (algebraMap K F)) (RingHom.id F ∘ T) x2 s2 := by
    simpa only [RingHom.id_comp, RingHom.coe_id, Function.id_comp] using h2
  have hk := h1.kaVal hL hA h2' hk1
  have hA2 : admitted x2.P.g n l l' al := by rw [h2.g_eq]; exact hA
  have e := GlobalTheory.T.keyInvariantFromIntersection_unique hL F x2 n l l' al s2 _ _ hA2 hk hk2
  rw [← e]
  rfl

/- English proof (translation)
Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap K Ω).injective`. Take `⟨x', s, hf⟩` from `exists_framed b (algebraMap K Ω) T`. Take `⟨φ, w, hg, b', H, hb', hs⟩` from `id hf`. Establish `hA' : admitted x'.P.g n l l' al` using `by rw [hg]; exact hA`. Establish `hinj : Function.Injective (fun p : Fin x'.P.g × Fin (n ^ x.P.g) => ((p.1.cast hg, p.2) : Fin x.P.g × Fin (n ^ x.P.g)))` using `fun p q hpq => Prod.ext (Fin.ext (congrArg (fun r => (r.1 : ℕ)) hpq)) (congrArg (fun r => r.2) hpq)`.

Take `⟨d, z, ch, hz⟩` from `GlobalTheory.T.generic_sections_meet_transversally hL K Ω x x' φ w n b b' (fun p => T (p.1.cast hg, p.2)) s hA.1 H hb hb' (hT.comp _ hinj) hs`. Take `⟨κ, hκ⟩` from `GlobalTheory.T.exists_keyInvariant_algClosed_transversal hL Ω x' n l l' al d s z ch hA' (Nat.cast_ne_zero.mpr (degProd_ne_zero hA')) hz`. Conclude with `⟨κ, x', s, κ, hf, hκ, rfl⟩`.
-/
theorem exists_valAt [CharZero K] (hL : Out.Laws) (hA : admitted x.P.g n l l' al) (hb : IsBasis x b) (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] [Algebra K Ω] (T : Fin x.P.g × Fin (n ^ x.P.g) → Ω) (hT : AlgebraicIndependent K T) :
    ∃ a, ValAt b l l' al Ω T a := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  obtain ⟨x', s, hf⟩ := exists_framed b (algebraMap K Ω) T
  obtain ⟨φ, w, hg, b', H, hb', hs⟩ := id hf
  have hA' : admitted x'.P.g n l l' al := by rw [hg]; exact hA
  have hinj : Function.Injective
      (fun p : Fin x'.P.g × Fin (n ^ x.P.g) => ((p.1.cast hg, p.2) : Fin x.P.g × Fin (n ^ x.P.g))) :=
    fun p q hpq => Prod.ext (Fin.ext (congrArg (fun r => (r.1 : ℕ)) hpq)) (congrArg (fun r => r.2) hpq)
  obtain ⟨d, z, ch, hz⟩ := GlobalTheory.T.generic_sections_meet_transversally hL K Ω x x' φ w n b b' (fun p => T (p.1.cast hg, p.2)) s hA.1 H hb hb'
    (hT.comp _ hinj) hs
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_keyInvariant_algClosed_transversal hL Ω x' n l l' al d s z ch hA'
    (Nat.cast_ne_zero.mpr (degProd_ne_zero hA')) hz
  exact ⟨κ, x', s, κ, hf, hκ, rfl⟩

/- English proof (translation)
Take `⟨x1, s1, κ1, h1, hk1, rfl⟩` from `h`. Take `⟨x2, s2, κ2, h2, hk2, rfl⟩` from `h'`. Take `⟨φ, w, hg, b', H, hb', hs1⟩` from `id h1`. Use `choose s3 hs3 using fun i : Fin x1.P.g => exists_coords x1 b' (fun k => T' (i.cast hg, k))`. Establish `h3 : Framed b (algebraMap K Ω) T' x1 s3` using `⟨φ, w, hg, b', H, hb', hs3⟩`.

Establish `h3' : Framed b ((RingHom.id Ω).comp (algebraMap K Ω)) (RingHom.id Ω ∘ T') x1 s3`. Simplify `h3` using `only [RingHom.id_comp, RingHom.coe_id, Function.id_comp]`. Establish `hk3` using `h2.kaVal hL hA h3' hk2`. Establish `hinj : Function.Injective (fun p : Fin x1.P.g × Fin (n ^ x.P.g) => ((p.1.cast hg, p.2) : Fin x.P.g × Fin (n ^ x.P.g)))` using `fun p q hpq => Prod.ext (Fin.ext (congrArg (fun r => (r.1 : ℕ)) hpq)) (congrArg (fun r => r.2) hpq)`. Establish `hind` using `hT.comp _ (Sum.map_injective.mpr ⟨hinj, hinj⟩)`.

Rewrite `hind` using `[Sum.elim_comp_map]`. Establish `e` using `GlobalTheory.T.keyInvariant_eq_of_independent_generic_tuples hL K Ω x x1 φ w n l l' al b b' (fun p => T (p.1.cast hg, p.2)) (fun p => T' (p.1.cast hg, p.2)) s1 s3 κ1 _ hA H hb hb' hind hs1 hs3 hk1 hk3`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem valAt_generic [CharZero K] (hL : Out.Laws) (hA : admitted x.P.g n l l' al) (hb : IsBasis x b) (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] [Algebra K Ω] (T T' : Fin x.P.g × Fin (n ^ x.P.g) → Ω) (a a' : Ω)
    (hT : AlgebraicIndependent K (Sum.elim T T')) (h : ValAt b l l' al Ω T a) (h' : ValAt b l l' al Ω T' a') :
    a = a' := by
  obtain ⟨x1, s1, κ1, h1, hk1, rfl⟩ := h
  obtain ⟨x2, s2, κ2, h2, hk2, rfl⟩ := h'
  obtain ⟨φ, w, hg, b', H, hb', hs1⟩ := id h1
  choose s3 hs3 using fun i : Fin x1.P.g => exists_coords x1 b' (fun k => T' (i.cast hg, k))
  have h3 : Framed b (algebraMap K Ω) T' x1 s3 := ⟨φ, w, hg, b', H, hb', hs3⟩
  have h3' : Framed b ((RingHom.id Ω).comp (algebraMap K Ω)) (RingHom.id Ω ∘ T') x1 s3 := by
    simpa only [RingHom.id_comp, RingHom.coe_id, Function.id_comp] using h3
  have hk3 := h2.kaVal hL hA h3' hk2
  have hinj : Function.Injective
      (fun p : Fin x1.P.g × Fin (n ^ x.P.g) => ((p.1.cast hg, p.2) : Fin x.P.g × Fin (n ^ x.P.g))) :=
    fun p q hpq => Prod.ext (Fin.ext (congrArg (fun r => (r.1 : ℕ)) hpq)) (congrArg (fun r => r.2) hpq)
  have hind := hT.comp _ (Sum.map_injective.mpr ⟨hinj, hinj⟩)
  rw [Sum.elim_comp_map] at hind
  have e := GlobalTheory.T.keyInvariant_eq_of_independent_generic_tuples hL K Ω x x1 φ w n l l' al b b' (fun p => T (p.1.cast hg, p.2))
    (fun p => T' (p.1.cast hg, p.2)) s1 s3 κ1 _ hA H hb hb' hind hs1 hs3 hk1 hk3
  rw [e]
  rfl

/- English proof (translation)
Take `⟨xΩ, sΩ, κ, hΩ, hκ, rfl⟩` from `h`. Take `⟨xO, sO, hO⟩` from `exists_framed b (algebraMap K O) T`. Establish `hΩ' : Framed b ((r : O →+* Ω).comp (algebraMap K O)) ((r : O →+* Ω) ∘ T) xΩ sΩ`. Rewrite using `[r.comp_algebraMap]`. Conclude with `hΩ`.

Take `⟨φ, w, hg, H, hs⟩` from `hO.via hΩ'`. Take `⟨z, ch, _, _, _, _, _, _, _, hz, _⟩` from `id hκ`. Establish `hAO : admitted xO.P.g n l l' al` using `by rw [hO.g_eq]; exact hA`. Establish `hu : IsUnit ((degProd xO.P.g n l l' : ℕ) : O)`. Establish `h0 : ((degProd xO.P.g n l l' : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.mpr (degProd_ne_zero hAO)`.

Use `(IsUnit.mk0 _ h0).map (algebraMap K O)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Take `⟨O', i1, i2, i3, j, r', x', φ', w', hg', s', u, hj, -, hr', H', hs', hu'⟩` from `GlobalTheory.T.exists_keyInvariant_after_dvr_extension hL O Ω (r : O →+* Ω) xO xΩ φ w n l l' al _ hg sO sΩ z ch hr hAO hu H hs hz`. Use `letI : Algebra K O' := (j.comp (algebraMap K O)).toAlgebra`. Set `jA : O →ₐ[K] O'` to `{ toRingHom := j, commutes' := fun c => rfl }`.

Set `rA : O' →ₐ[K] Ω` to `{ toRingHom := r', commutes' := fun c => by show r' (j (algebraMap K O c)) = algebraMap K Ω c`. Rewrite using `[← RingHom.comp_apply, hr']`. Conclude with `r.commutes c }`. Use `⟨O', i1, i2, i3, inferInstance, jA, rA, (u : O'), hj, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `c show r' (j c) = r c`.

Rewrite using `[← RingHom.comp_apply, hr']`. Both sides reduce to the same expression. Take `⟨x'', s'', h''⟩` from `exists_framed b (algebraMap K O') (jA ∘ T)`. Establish `h2 : Framed b (j.comp (algebraMap K O)) (j ∘ T) x'' s''` using `h''`. Take `⟨φ2, w2, hg2, H2, hs2⟩` from `hO.via h2`.

Establish `H2' : KeyVia x'' xO ((RingHom.id O').comp j) φ2 w2` using `by rw [RingHom.id_comp]; exact H2`. Take `⟨φ3, w3, H3, -, hsec⟩` from `GlobalTheory.KaLift.keyVia_cancel H' H2'`. Establish `hg3 : x''.P.g = x'.P.g` using `hg2.trans hg'.symm`. Establish `hs3 : ∀ i, SecVia x'' x' φ3 w3 (s'' i) (s' (i.cast hg3))`. Introduce `i`.

Establish `h1` using `hs' (i.cast hg3)`. Establish `e : (i.cast hg3).cast hg' = i.cast hg2` using `Fin.ext rfl`. Rewrite `h1` using `[e]`. Conclude with `hsec n (sO (i.cast hg2)) (s' (i.cast hg3)) (s'' i) h1 (hs2 i)`. Establish `hA' : admitted x'.P.g n l l' al` using `by rw [hg']; exact hAO`.

Establish `hk` using `GlobalTheory.T.keyInvariant_baseChange hL O' O' x' x'' (RingHom.id O') φ3 w3 n l l' al hg3 s' s'' u hA' H3 hs3 hu'`. Conclude with `⟨x'', s'', _, h'', hk, rfl⟩`.
-/
theorem valAt_lift [CharZero K] (hL : Out.Laws) (hA : admitted x.P.g n l l' al) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra K O] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (r : O →ₐ[K] Ω)
    (T : Fin x.P.g × Fin (n ^ x.P.g) → O) (a : Ω) (hr : RingHom.ker r = IsLocalRing.maximalIdeal O)
    (h : ValAt b l l' al Ω (r ∘ T) a) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : Algebra K O')
      (j : O →ₐ[K] O') (r' : O' →ₐ[K] Ω) (u : O'), Function.Injective j ∧ r'.comp j = r ∧
        ValAt b l l' al O' (j ∘ T) u := by
  obtain ⟨xΩ, sΩ, κ, hΩ, hκ, rfl⟩ := h
  obtain ⟨xO, sO, hO⟩ := exists_framed b (algebraMap K O) T
  have hΩ' : Framed b ((r : O →+* Ω).comp (algebraMap K O)) ((r : O →+* Ω) ∘ T) xΩ sΩ := by
    rw [r.comp_algebraMap]; exact hΩ
  obtain ⟨φ, w, hg, H, hs⟩ := hO.via hΩ'
  obtain ⟨z, ch, _, _, _, _, _, _, _, hz, _⟩ := id hκ
  have hAO : admitted xO.P.g n l l' al := by rw [hO.g_eq]; exact hA
  have hu : IsUnit ((degProd xO.P.g n l l' : ℕ) : O) := by
    have h0 : ((degProd xO.P.g n l l' : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (degProd_ne_zero hAO)
    have := (IsUnit.mk0 _ h0).map (algebraMap K O)
    rwa [map_natCast] at this
  obtain ⟨O', i1, i2, i3, j, r', x', φ', w', hg', s', u, hj, -, hr', H', hs', hu'⟩ :=
    GlobalTheory.T.exists_keyInvariant_after_dvr_extension hL O Ω (r : O →+* Ω) xO xΩ φ w n l l' al _ hg sO sΩ z ch hr hAO hu H hs hz
  letI : Algebra K O' := (j.comp (algebraMap K O)).toAlgebra
  let jA : O →ₐ[K] O' := { toRingHom := j, commutes' := fun c => rfl }
  let rA : O' →ₐ[K] Ω :=
    { toRingHom := r', commutes' := fun c => by
        show r' (j (algebraMap K O c)) = algebraMap K Ω c
        rw [← RingHom.comp_apply, hr']
        exact r.commutes c }
  refine ⟨O', i1, i2, i3, inferInstance, jA, rA, (u : O'), hj, ?_, ?_⟩
  · ext c
    show r' (j c) = r c
    rw [← RingHom.comp_apply, hr']
    rfl
  · obtain ⟨x'', s'', h''⟩ := exists_framed b (algebraMap K O') (jA ∘ T)
    have h2 : Framed b (j.comp (algebraMap K O)) (j ∘ T) x'' s'' := h''
    obtain ⟨φ2, w2, hg2, H2, hs2⟩ := hO.via h2
    have H2' : KeyVia x'' xO ((RingHom.id O').comp j) φ2 w2 := by rw [RingHom.id_comp]; exact H2
    obtain ⟨φ3, w3, H3, -, hsec⟩ := GlobalTheory.KaLift.keyVia_cancel H' H2'
    have hg3 : x''.P.g = x'.P.g := hg2.trans hg'.symm
    have hs3 : ∀ i, SecVia x'' x' φ3 w3 (s'' i) (s' (i.cast hg3)) := by
      intro i
      have h1 := hs' (i.cast hg3)
      have e : (i.cast hg3).cast hg' = i.cast hg2 := Fin.ext rfl
      rw [e] at h1
      exact hsec n (sO (i.cast hg2)) (s' (i.cast hg3)) (s'' i) h1 (hs2 i)
    have hA' : admitted x'.P.g n l l' al := by rw [hg']; exact hAO
    have hk := GlobalTheory.T.keyInvariant_baseChange hL O' O' x' x'' (RingHom.id O') φ3 w3 n l l' al hg3 s' s'' u hA' H3 hs3 hu'
    exact ⟨x'', s'', _, h'', hk, rfl⟩

/- English proof (translation)
Introduce `hL K _ _ _ x n l l' al hA`. Take `⟨⟨b, hb⟩, hpull⟩` from `GlobalTheory.KeyBasis.main hL K x n (by have := hA.1; omega)`. Take `⟨κ0, hall, hgen⟩` from `GlobalTheory.GenericValue.exists_value (K := K) (fun (R : Type) [CommRing R] [Algebra K R] (T : Fin x.P.g × Fin (n ^ x.P.g) → R) (a : R) => ValAt b l l' al R T a) (valAt_map (b := b) hL hA) (valAt_unique (b := b) hL hA) (exists_valAt (b := b) hL hA hb) (valAt_generic (b := b) hL …`. Take `⟨xG, sG, κG, hfG, hkG, hG⟩` from `hgen`. Establish `hκ0 : κ0 ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hG` using `[map_zero]`. Conclude with `κG.ne_zero hG.symm`. Use `⟨Units.mk0 κ0 hκ0, ?_, ?_⟩` and prove the remaining obligations. Introduce `K' _ _ f x' s' κ' hx' hk'`.

Use `letI : Algebra K K' := f.toAlgebra`. Take `⟨φ, w, H⟩` from `(GlobalTheory.KeyVia.main K K' x x' f).1.1 hx'`. Take `⟨_, hg, _⟩` from `id H`. Establish `M` using `(GlobalTheory.KeyVia.main K K' x x' f).2 φ w H`. Use `choose b' hb' _ using fun k => M.1 n (b k)`.

Establish `hbas : IsBasis x' b'` using `(hpull b hb K' f x' φ w b' H hb')`. Use `choose c hc _ using fun i : Fin x.P.g => hbas (s' (i.cast hg.symm))`. Establish `hf : Framed b (algebraMap K K') (fun p => c p.1 p.2) x' s'`. Use `⟨φ, w, hg, b', H, hb', fun i => ?_⟩` and prove the remaining obligations. Establish `e : (i.cast hg).cast hg.symm = i` using `Fin.ext rfl`.

Establish `h1` using `hc (i.cast hg)`. Rewrite `h1` using `[e]`. Conclude with `h1`. Establish `h2` using `hall K' (fun p => c p.1 p.2) κ' ⟨x', s', κ', hf, hk', rfl⟩`. Rewrite using `[h2, Units.val_mk0]`.

Both sides reduce to the same expression. Take `⟨φ, w, hg, b', H, -, -⟩` from `hfG`. Conclude with `⟨_, inferInstance, inferInstance, algebraMap K _, xG, φ, w, sG, κG, H, hkG⟩`.
-/
theorem kaVal_independent : Out.Laws → ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (x : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ), admitted x.P.g n l l' al → ∃ κ : Kˣ, (∀ (K' : Type) [Field K'] [IsAlgClosed K'] (f : K →+* K') (x' : KeyIn K') (s' : Fin x'.P.g → RR x' n) (κ' : K'ˣ), KeyPB x' x f → KaVal x' n l l' al s' κ' → (κ' : K') = f κ) ∧ ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K') (f : K →+* K') (x' : KeyIn K') (φ : _) (w : _) (s' : Fin x'.P.g → RR x' n) (κ' : K'ˣ), KeyVia x' x f φ w ∧ KaVal x' n l l' al s' κ' := by
  intro hL K _ _ _ x n l l' al hA
  obtain ⟨⟨b, hb⟩, hpull⟩ := GlobalTheory.KeyBasis.main hL K x n (by have := hA.1; omega)
  obtain ⟨κ0, hall, hgen⟩ := GlobalTheory.GenericValue.exists_value (K := K)
    (fun (R : Type) [CommRing R] [Algebra K R] (T : Fin x.P.g × Fin (n ^ x.P.g) → R) (a : R) =>
      ValAt b l l' al R T a)
    (valAt_map (b := b) hL hA) (valAt_unique (b := b) hL hA) (exists_valAt (b := b) hL hA hb)
    (valAt_generic (b := b) hL hA hb) (valAt_lift (b := b) hL hA)
  obtain ⟨xG, sG, κG, hfG, hkG, hG⟩ := hgen
  have hκ0 : κ0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hG
    exact κG.ne_zero hG.symm
  refine ⟨Units.mk0 κ0 hκ0, ?_, ?_⟩
  · intro K' _ _ f x' s' κ' hx' hk'
    letI : Algebra K K' := f.toAlgebra
    obtain ⟨φ, w, H⟩ := (GlobalTheory.KeyVia.main K K' x x' f).1.1 hx'
    obtain ⟨_, hg, _⟩ := id H
    have M := (GlobalTheory.KeyVia.main K K' x x' f).2 φ w H
    choose b' hb' _ using fun k => M.1 n (b k)
    have hbas : IsBasis x' b' := (hpull b hb K' f x' φ w b' H hb')
    choose c hc _ using fun i : Fin x.P.g => hbas (s' (i.cast hg.symm))
    have hf : Framed b (algebraMap K K') (fun p => c p.1 p.2) x' s' := by
      refine ⟨φ, w, hg, b', H, hb', fun i => ?_⟩
      have e : (i.cast hg).cast hg.symm = i := Fin.ext rfl
      have h1 := hc (i.cast hg)
      rw [e] at h1
      exact h1
    have h2 := hall K' (fun p => c p.1 p.2) κ' ⟨x', s', κ', hf, hk', rfl⟩
    rw [h2, Units.val_mk0]
    rfl
  · obtain ⟨φ, w, hg, b', H, -, -⟩ := hfG
    exact ⟨_, inferInstance, inferInstance, algebraMap K _, xG, φ, w, sG, κG, H, hkG⟩

end GlobalTheory.KaIndep
