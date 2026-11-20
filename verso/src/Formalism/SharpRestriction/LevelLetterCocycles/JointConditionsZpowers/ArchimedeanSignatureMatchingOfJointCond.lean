import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

section Roots

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Unfold `Formalism.CyclotomicNorms.rootsBar`. Rewrite using `[Polynomial.map_mul, Polynomial.roots_mul]`. Establish `hi : Function.Injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))` using `(algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective`. Conclude with `mul_ne_zero ((Polynomial.map_ne_zero_iff hi).2 ha) ((Polynomial.map_ne_zero_iff hi).2 hb)`.
-/
theorem rootsBar_mul (a b : (ZMod g)[X]) (ha : a ≠ 0) (hb : b ≠ 0) :
    Formalism.CyclotomicNorms.rootsBar (a * b) = Formalism.CyclotomicNorms.rootsBar a + Formalism.CyclotomicNorms.rootsBar b := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_mul, Polynomial.roots_mul]
  have hi : Function.Injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) := (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
  exact mul_ne_zero ((Polynomial.map_ne_zero_iff hi).2 ha) ((Polynomial.map_ne_zero_iff hi).2 hb)

/- English proof (translation)
Unfold `Formalism.CyclotomicNorms.rootsBar`. Rewrite using `[Polynomial.map_pow, Polynomial.roots_pow]`.
-/
theorem rootsBar_pow (a : (ZMod g)[X]) (d : ℕ) : Formalism.CyclotomicNorms.rootsBar (a ^ d) = d • Formalism.CyclotomicNorms.rootsBar a := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_pow, Polynomial.roots_pow]

/- English proof (translation)
Unfold `Formalism.CyclotomicNorms.rootsBar`. Rewrite using `[Polynomial.map_one, Polynomial.roots_one]`. Both sides reduce to the same expression.
-/
theorem rootsBar_one : Formalism.CyclotomicNorms.rootsBar (1 : (ZMod g)[X]) = 0 := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_one, Polynomial.roots_one]
  rfl

/- English proof (translation)
Unfold `Formalism.CyclotomicNorms.rootsBar`. Rewrite using `[Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits (a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)))), Polynomial.natDegree_map]`.
-/
theorem card_rootsBar (a : (ZMod g)[X]) : Multiset.card (Formalism.CyclotomicNorms.rootsBar a) = a.natDegree := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits (a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)))),
    Polynomial.natDegree_map]

/- English proof (translation)
Unfold `Formalism.CyclotomicNorms.rootsBar`. Establish `hbij : Function.Bijective (frobenius (Formalism.CyclotomicNorms.Fbar g) g)` using `PerfectRing.bijective_frobenius`. Set `F : Formalism.CyclotomicNorms.Fbar g ≃+* Formalism.CyclotomicNorms.Fbar g` to `RingEquiv.ofBijective (frobenius (Formalism.CyclotomicNorms.Fbar g) g) hbij`. Establish `h1 : ((a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))).map (F : Formalism.CyclotomicNorms.Fbar g →+* Formalism.CyclotomicNorms.Fbar g)) = a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))`. Rewrite using `[Polynomial.map_map]`.

Use `congr 1`. Use extensionality with `c`. Use `show (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c) ^ g = _`. Rewrite using `[← map_pow, ZMod.pow_card]`. Establish `h2` using `Polynomial.roots_map_of_injective_of_card_eq_natDegree (p := a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))) (f := (F : Formalism.CyclotomicNorms.Fbar g →+* Formalism.CyclotomicNorms.Fbar g)) F.injective (Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _))`.

Rewrite `h2` using `[h1]`. Conclude with `h2`.
-/
theorem rootsBar_frob (a : (ZMod g)[X]) :
    (Formalism.CyclotomicNorms.rootsBar a).map (fun x => x ^ g) = Formalism.CyclotomicNorms.rootsBar a := by
  unfold Formalism.CyclotomicNorms.rootsBar
  have hbij : Function.Bijective (frobenius (Formalism.CyclotomicNorms.Fbar g) g) := PerfectRing.bijective_frobenius
  let F : Formalism.CyclotomicNorms.Fbar g ≃+* Formalism.CyclotomicNorms.Fbar g := RingEquiv.ofBijective (frobenius (Formalism.CyclotomicNorms.Fbar g) g) hbij
  have h1 : ((a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))).map (F : Formalism.CyclotomicNorms.Fbar g →+* Formalism.CyclotomicNorms.Fbar g)) =
      a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) := by
    rw [Polynomial.map_map]
    congr 1
    ext c
    show (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c) ^ g = _
    rw [← map_pow, ZMod.pow_card]
  have h2 := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (p := a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))) (f := (F : Formalism.CyclotomicNorms.Fbar g →+* Formalism.CyclotomicNorms.Fbar g)) F.injective
    (Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _))
  rw [h1] at h2
  exact h2

end Roots

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact rootsBar_one`. Consider the case `cons a l ih`. Establish `hl : ∀ b ∈ l, b ≠ 0` using `fun b hb => h b (List.mem_cons_of_mem _ hb)`. Rewrite using `[List.prod_cons, List.map_cons, List.sum_cons, rootsBar_mul a l.prod (h a List.mem_cons_self) (List.prod_ne_zero (fun h0 => hl 0 h0 rfl)), ih hl]`.
-/
theorem rootsBar_list_prod {g : ℕ} [Fact g.Prime] (l : List (ZMod g)[X]) (h : ∀ a ∈ l, a ≠ 0) :
    Formalism.CyclotomicNorms.rootsBar l.prod = (l.map Formalism.CyclotomicNorms.rootsBar).sum := by
  induction l with
  | nil => exact rootsBar_one
  | cons a l ih =>
    have hl : ∀ b ∈ l, b ≠ 0 := fun b hb => h b (List.mem_cons_of_mem _ hb)
    rw [List.prod_cons, List.map_cons, List.sum_cons,
      rootsBar_mul a l.prod (h a List.mem_cons_self) (List.prod_ne_zero (fun h0 => hl 0 h0 rfl)), ih hl]

section Lab

variable (D : D7)
  (hTw : ∀ (k : Fin 2) (w : PlE D.host) (a : D.naut.LP w) (s : ℝ),
    D.naut.items₂ k w (D.naut.lpTw a s) = D.naut.items₂ k w a)

include hTw

/- English proof (translation)
Establish `key : ∀ l : List ℝ, D.naut.items₂ k w (l.foldr (fun (j : ℝ) acc => D.naut.lpSum (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - j)) acc) (D.naut.lpZero w)) = (D.naut.items₂ k w (D.naut.locG p.π w)) ^ l.length`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => simp [D.naut.inertiaCharpoly_zero]`. Consider the case `cons j l ih => rw [List.foldr_cons, D.naut.inertiaCharpoly_add, hTw, ih, List.length_cons, pow_succ, mul_comm]`.

Unfold `spehLoc`. Rewrite using `[key]`. Simplify using the standard rewrite rules.
-/
theorem inertiaCharpoly_speh_eq_pow (k : Fin 2) (w : PlE D.host) (p : BasicNotions.Part D.naut.CG) :
    D.naut.items₂ k w (spehLoc D.nd D.naut p w) = (D.naut.items₂ k w (D.naut.locG p.π w)) ^ p.d := by
  have key : ∀ l : List ℝ, D.naut.items₂ k w (l.foldr (fun (j : ℝ) acc =>
      D.naut.lpSum (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - j)) acc) (D.naut.lpZero w)) =
      (D.naut.items₂ k w (D.naut.locG p.π w)) ^ l.length := by
    intro l
    induction l with
    | nil => simp [D.naut.inertiaCharpoly_zero]
    | cons j l ih => rw [List.foldr_cons, D.naut.inertiaCharpoly_add, hTw, ih, List.length_cons, pow_succ, mul_comm]
  unfold spehLoc
  rw [key]
  simp

/- English proof (translation)
Proceed by induction on `Sig with`. Consider the case `nil => simp [isoLoc, D.naut.inertiaCharpoly_zero]`. Consider the case `cons p Sig ih`. Rewrite using `[List.map_cons, List.prod_cons, ← ih, ← inertiaCharpoly_speh_eq_pow D hTw]`. Conclude with `D.naut.inertiaCharpoly_add _ _ _ _`.
-/
theorem inertiaCharpoly_eq_of_iso (k : Fin 2) (w : PlE D.host) (Sig : List (BasicNotions.Part D.naut.CG)) :
    D.naut.items₂ k w (isoLoc D.nd D.naut Sig w) =
      (Sig.map fun p => (D.naut.items₂ k w (D.naut.locG p.π w)) ^ p.d).prod := by
  induction Sig with
  | nil => simp [isoLoc, D.naut.inertiaCharpoly_zero]
  | cons p Sig ih =>
    rw [List.map_cons, List.prod_cons, ← ih, ← inertiaCharpoly_speh_eq_pow D hTw]
    exact D.naut.inertiaCharpoly_add _ _ _ _

end Lab

def IsBcSig (D : D7) (i : D.nd.Loc) (σ : D.what₂.FT) (Sig : List (Part D.naut.CG)) : Prop :=
  D.what₂.isot (D.nd.j i) σ ≠ ⊥ ∧ HasParamW D.nd D.naut i σ Sig ∧ (∃ P, thetaOf D.nd D.naut i σ P) ∧
    ∀ P, thetaOf D.nd D.naut i σ P →
      IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv)

def GlobalDatumTwistCondition (D : D7) : Prop :=
  (∀ σ : D.what₂.FT, ∃ i : D.nd.Loc, D.what₂.isot (D.nd.j i) σ ≠ ⊥) ∧
  (∀ i σ Sig, IsBcSig D i σ Sig → ∀ p ∈ Sig, D.naut.csd p.π) ∧
  (∀ (k : Fin 2) (w : PlE D.host) (a : D.naut.LP w) (s : ℝ),
    D.naut.items₂ k w (D.naut.lpTw a s) = D.naut.items₂ k w a) ∧
  (∀ i σ Sig, IsBcSig D i σ Sig → ∀ p ∈ Sig, ∀ (k : Fin 2) (v : D.nd.PlG k),
    (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v))).natDegree = p.a) ∧
  (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) ∧
  (∀ i σ Sig, IsBcSig D i σ Sig → ∀ p ∈ Sig, ∀ τ, (D.naut.infG p.π τ).Nodup ∧
    ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.r : ℂ) - (p.d : ℂ)) / 2)

def GlobalDatumTwistDualCondition (D : D7) : Prop :=
  ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k),
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (D.ntypes.cuspidal σ →
      Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) →
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ D.host.g k →
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      Matrix.charpoly ((D.ntypes.rbar σ w (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
          X - C (D.ntypes.iota k v w (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar w) x))).prod ∧
      ∃ φ : G D.host.E D.nd.Om,
        D.ntypes.rbar σ w (φ * D.ntypes.tg k v * φ⁻¹) = D.ntypes.rbar σ w (D.ntypes.tg k v) ^ D.host.g k)

/- English proof (translation)
Introduce `σ k v`. Use `⟨?_, hb σ k v⟩` and prove the remaining obligations. Establish `: Fact (D.host.g k).Prime` using `⟨D.host.g_prime k⟩`. Take `⟨hocc, hcsd, hTw, hdz, hsp, hreg⟩` from `ha`. Take `⟨i, hi⟩` from `hocc σ`.

Take `⟨Sig, hSig, hBCV⟩` from `(h42 i σ hi).2.1`. Establish `hBc : IsBcSig D i σ Sig` using `⟨hi, hSig, (h42 i σ hi).1.2, hBCV⟩`. Establish `hlab : D.nd.lab k σ v = (Sig.map fun p => (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v))) ^ p.d).prod`. Rewrite using `[D.naut.lab_loc i k σ v, ← hSig.2.2 _ (hsp k v), inertiaCharpoly_eq_of_iso D hTw]`. Establish `hne : ∀ p ∈ Sig, D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v)) ≠ 0`.

Introduce `p hp h0`. Establish `h1` using `hdz i σ Sig hBc p hp k v`. Rewrite `h1` using `[h0, Polynomial.natDegree_zero]`. Use `(hSig.1 p hp).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `⟨Sig.map fun p => (p.a, p.d, Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v)))), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[D.bc_tie i σ Sig hSig (hcsd i σ Sig hBc) (hreg i σ Sig hBc), List.map_map]`. Both sides reduce to the same expression. Introduce `q hq`. Take `⟨p, hp, rfl⟩` from `List.mem_map.1 hq`.

Conclude with `⟨by rw [card_rootsBar]; exact hdz i σ Sig hBc p hp k v, rootsBar_frob _⟩`. Rewrite using `[hlab, rootsBar_list_prod, List.map_map, List.map_map]`. Use `congr 1`. Use `List.map_congr_left fun p _ => ?_` and prove the remaining obligations. Conclude with `rootsBar_pow _ _`.

Introduce `a ha'`. Take `⟨p, hp, rfl⟩` from `List.mem_map.1 ha'`. Conclude with `pow_ne_zero _ (hne p hp)`.
-/
theorem archimedeanSignatureMatching_of_jointCond (D : D7) (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D) (ha : GlobalDatumTwistCondition D) (hb : GlobalDatumTwistDualCondition D) :
    Formalism.MainNotions.ArithmeticCylinders.ArchimedeanSignatureMatching D := by
  intro σ k v
  refine ⟨?_, hb σ k v⟩
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨hocc, hcsd, hTw, hdz, hsp, hreg⟩ := ha
  obtain ⟨i, hi⟩ := hocc σ
  obtain ⟨Sig, hSig, hBCV⟩ := (h42 i σ hi).2.1
  have hBc : IsBcSig D i σ Sig := ⟨hi, hSig, (h42 i σ hi).1.2, hBCV⟩
  have hlab : D.nd.lab k σ v = (Sig.map fun p =>
      (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v))) ^ p.d).prod := by
    rw [D.naut.lab_loc i k σ v, ← hSig.2.2 _ (hsp k v), inertiaCharpoly_eq_of_iso D hTw]
  have hne : ∀ p ∈ Sig, D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v)) ≠ 0 := by
    intro p hp h0
    have h1 := hdz i σ Sig hBc p hp k v
    rw [h0, Polynomial.natDegree_zero] at h1
    have := (hSig.1 p hp).1
    omega
  refine ⟨Sig.map fun p => (p.a, p.d,
    Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v)))), ?_, ?_, ?_⟩
  · rw [D.bc_tie i σ Sig hSig (hcsd i σ Sig hBc) (hreg i σ Sig hBc), List.map_map]
    rfl
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact ⟨by rw [card_rootsBar]; exact hdz i σ Sig hBc p hp k v, rootsBar_frob _⟩
  · rw [hlab, rootsBar_list_prod, List.map_map, List.map_map]
    · congr 1
      refine List.map_congr_left fun p _ => ?_
      exact rootsBar_pow _ _
    · intro a ha'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha'
      exact pow_ne_zero _ (hne p hp)

end Formalism.MainNotions.N
