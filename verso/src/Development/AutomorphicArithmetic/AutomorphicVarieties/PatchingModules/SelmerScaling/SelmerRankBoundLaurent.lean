import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelScale1

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Use `show DD.map f (DD.C c * u) = DD.C (f c) * DD.map f u`. Rewrite using `[map_mul]`. Use `congr 1`. Apply `DD.ext` to reduce the goal to its premises. Both sides reduce to the same expression.

Use function extensionality and compare the values at `j`. Conclude with `map_zero f`. Use function extensionality and compare the values at `j`. Conclude with `map_zero f`. Conclude with `map_zero f`.
-/
private theorem dual_numbers_map_smul {X Y : Type} [CommRing X] [CommRing Y] {g : ℕ} (f : X →+* Y) (c : X) (u : DD X g) :
    DD.map f (c • u) = f c • DD.map f u := by
  show DD.map f (DD.C c * u) = DD.C (f c) * DD.map f u
  rw [map_mul]
  congr 1
  apply DD.ext
  · rfl
  · funext j
    exact map_zero f
  · funext j
    exact map_zero f
  · exact map_zero f

/- English proof (translation)
Establish `hE : (DD.map (algebraMap x.A x.Fr)).mapMatrix (DD.epM fun j => (k.κ j g).map (algebraMap x.A x.A)) = DD.epM fun j => (k.κ j g).map (algebraMap x.A x.Fr)`. Apply the tactic sequence `ext a b <;> simp [DD.epM, DD.map, RingHom.mapMatrix_apply]`. Establish `hR : (DD.map (algebraMap x.A x.Fr)).mapMatrix (x.ρX (DD x.A k.g) g) = x.ρX (DD x.Fr k.g) g`. Apply the tactic sequence `ext a b <;> simp [NP.ρX, DD.map, RingHom.mapMatrix_apply]`. Apply the tactic sequence `all_goals first | rfl | exact map_zero _`.

Unfold `Kap.ρ1`. Rewrite using `[map_mul, map_add, map_one, hE, hR]`.
-/
private theorem map_first_order_lift_residue_field {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (g : F.G₀) :
    (DD.map (algebraMap x.A x.Fr)).mapMatrix (k.ρ1 x.A g) = k.ρ1 x.Fr g := by
  have hE : (DD.map (algebraMap x.A x.Fr)).mapMatrix (DD.epM fun j => (k.κ j g).map (algebraMap x.A x.A))
      = DD.epM fun j => (k.κ j g).map (algebraMap x.A x.Fr) := by
    ext a b <;> simp [DD.epM, DD.map, RingHom.mapMatrix_apply]
  have hR : (DD.map (algebraMap x.A x.Fr)).mapMatrix (x.ρX (DD x.A k.g) g) = x.ρX (DD x.Fr k.g) g := by
    ext a b <;> simp [NP.ρX, DD.map, RingHom.mapMatrix_apply]
    all_goals first | rfl | exact map_zero _
  unfold Kap.ρ1
  rw [map_mul, map_add, map_one, hE, hR]

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `hu`. Use `⟨fun hb => ?_, fun hb => ?_, fun hb => ?_, fun hb => ?_⟩` and prove the remaining obligations. Use `show algebraMap A Y u.a = 0`. Rewrite using `[h1 hb, map_zero]`. Use `show (fun j => algebraMap A Y (u.ep j)) = 0`.

Rewrite using `[h2 hb]`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Use `show (fun j => algebraMap A Y (u.ep' j)) = 0`. Rewrite using `[h3 hb]`.

Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Use `show algebraMap A Y u.eta = 0`. Rewrite using `[h4 hb, map_zero]`.
-/
private theorem map_mem_dual_numbers_part {A Y : Type} [CommRing A] [CommRing Y] [Algebra A Y] {g : ℕ} {b1 b2 b3 b4 : Bool} {u : DD A g}
    (hu : u ∈ ddPart A A g b1 b2 b3 b4) : DD.map (algebraMap A Y) u ∈ ddPart A Y g b1 b2 b3 b4 := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨fun hb => ?_, fun hb => ?_, fun hb => ?_, fun hb => ?_⟩
  · show algebraMap A Y u.a = 0
    rw [h1 hb, map_zero]
  · show (fun j => algebraMap A Y (u.ep j)) = 0
    rw [h2 hb]
    funext j
    simp
  · show (fun j => algebraMap A Y (u.ep' j)) = 0
    rw [h3 hb]
    funext j
    simp
  · show algebraMap A Y u.eta = 0
    rw [h4 hb, map_zero]

/- English proof (translation)
Introduce `l _ L G G0 h n x k D0 hK e z hz hind`. Use `choose s₀ hs₀ using fun i => selScale1 l L G G0 h n x k (z i) (hz i).1 (hz i).2`. Take `⟨z', hz'S, hz'map⟩ : ∃ z' : Fin e → G.frame.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g), (∀ i, z' i ∈ Sel1 h x.A k) ∧ ∀ i g, (z' i g).map (DD.map (algebraMap x.A x.Fr)) = (algebraMap x.A x.Fr) x.t ^ (Finset.univ.sup s₀) • z i g` from `by choose z' hz'S hz'map using fun i => hs₀ i (Finset.univ.sup s₀) (Finset.le_sup (Finset.mem_univ i))`. Conclude with `⟨z', hz'S, hz'map⟩`. Apply `hK e z' hz'S` to reduce the goal to its premises.

Introduce `c hc`. Take `⟨Y, hY, hYt, hYeq⟩` from `hc`. Establish `hmapSmul : ∀ (c0 : x.A) (M : Matrix (Fin n) (Fin n) (DD x.A k.g)), (DD.map (algebraMap x.A x.Fr)).mapMatrix (c0 • M) = algebraMap x.A x.Fr c0 • (DD.map (algebraMap x.A x.Fr)).mapMatrix M`. Introduce `c0 M`. Conclude with `Matrix.ext fun a b => dual_numbers_map_smul (algebraMap x.A x.Fr) c0 (M a b)`.

Establish `key : ∑ i, (algebraMap x.A x.Fr (c i) * algebraMap x.A x.Fr x.t ^ (Finset.univ.sup s₀)) • z i ∈ Bd1 h x.Fr k`. Simplify using `only [Bd1, Bd, Set.mem_setOf_eq]`. Use `⟨(DD.map (algebraMap x.A x.Fr)).mapMatrix Y, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b`. Conclude with `⟨fun hab => map_mem_dual_numbers_part ((hY a b).1 hab), fun hab => map_mem_dual_numbers_part ((hY a b).2 hab)⟩`.

Use `Matrix.ext fun a b => ?_ show DD.map (algebraMap x.A x.Fr) (Y b a) = -(DD.map (algebraMap x.A x.Fr) (Y a b))` and prove the remaining obligations. Rewrite using `[← map_neg]`. Use `congr 1`. Conclude with `congrFun (congrFun hYt a) b`. Use function extensionality and compare the values at `g`.

Establish `h1` using `congrFun hYeq g`. Establish `hsum : (DD.map (algebraMap x.A x.Fr)).mapMatrix (∑ i, c i • z' i g) = ∑ i, (algebraMap x.A x.Fr (c i) * algebraMap x.A x.Fr x.t ^ (Finset.univ.sup s₀)) • z i g`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hmapSmul, show (DD.map (algebraMap x.A x.Fr)).mapMatrix (z' i g) = algebraMap x.A x.Fr x.t ^ (Finset.univ.sup s₀) • z i g from hz'map i g, smul_smul]`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply] at h1 ⊢`. Rewrite using `[← hsum, h1]`. Simplify using `only [dY, map_sub, map_mul, map_first_order_lift_residue_field]`. Establish `hc'` using `hind _ key`. Establish `ht : algebraMap x.A x.Fr x.t ≠ 0` using `fun h0 => PowerSeries.X_ne_zero ((IsFractionRing.injective x.A x.Fr) (h0.trans (map_zero _).symm))`.

Use function extensionality and compare the values at `i`. Establish `hi` using `congrFun hc' i`. Conclude with `(IsFractionRing.injective x.A x.Fr) (((mul_eq_zero.mp hi).resolve_right (pow_ne_zero _ ht)).trans (map_zero _).symm)`.
-/
theorem UpperTheory.V.Pa.k1F :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ D0, K1 h k D0 → SelmerRankBoundLaurent h k D0 := by
  intro l _ L G G0 h n x k D0 hK e z hz hind
  classical
  choose s₀ hs₀ using fun i => selScale1 l L G G0 h n x k (z i) (hz i).1 (hz i).2
  obtain ⟨z', hz'S, hz'map⟩ : ∃ z' : Fin e → G.frame.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g),
      (∀ i, z' i ∈ Sel1 h x.A k) ∧ ∀ i g, (z' i g).map (DD.map (algebraMap x.A x.Fr))
        = (algebraMap x.A x.Fr) x.t ^ (Finset.univ.sup s₀) • z i g := by
    choose z' hz'S hz'map using fun i => hs₀ i (Finset.univ.sup s₀) (Finset.le_sup (Finset.mem_univ i))
    exact ⟨z', hz'S, hz'map⟩
  apply hK e z' hz'S
  intro c hc
  obtain ⟨Y, hY, hYt, hYeq⟩ := hc
  have hmapSmul : ∀ (c0 : x.A) (M : Matrix (Fin n) (Fin n) (DD x.A k.g)),
      (DD.map (algebraMap x.A x.Fr)).mapMatrix (c0 • M)
        = algebraMap x.A x.Fr c0 • (DD.map (algebraMap x.A x.Fr)).mapMatrix M := by
    intro c0 M
    exact Matrix.ext fun a b => dual_numbers_map_smul (algebraMap x.A x.Fr) c0 (M a b)
  have key : ∑ i, (algebraMap x.A x.Fr (c i) * algebraMap x.A x.Fr x.t ^ (Finset.univ.sup s₀)) • z i
      ∈ Bd1 h x.Fr k := by
    simp only [Bd1, Bd, Set.mem_setOf_eq]
    refine ⟨(DD.map (algebraMap x.A x.Fr)).mapMatrix Y, ?_, ?_, ?_⟩
    · intro a b
      exact ⟨fun hab => map_mem_dual_numbers_part ((hY a b).1 hab), fun hab => map_mem_dual_numbers_part ((hY a b).2 hab)⟩
    · refine Matrix.ext fun a b => ?_
      show DD.map (algebraMap x.A x.Fr) (Y b a) = -(DD.map (algebraMap x.A x.Fr) (Y a b))
      rw [← map_neg]
      congr 1
      exact congrFun (congrFun hYt a) b
    · funext g
      have h1 := congrFun hYeq g
      have hsum : (DD.map (algebraMap x.A x.Fr)).mapMatrix (∑ i, c i • z' i g)
          = ∑ i, (algebraMap x.A x.Fr (c i) * algebraMap x.A x.Fr x.t ^ (Finset.univ.sup s₀)) • z i g := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hmapSmul, show (DD.map (algebraMap x.A x.Fr)).mapMatrix (z' i g)
          = algebraMap x.A x.Fr x.t ^ (Finset.univ.sup s₀) • z i g from hz'map i g, smul_smul]
      simp only [Finset.sum_apply, Pi.smul_apply] at h1 ⊢
      rw [← hsum, h1]
      simp only [dY, map_sub, map_mul, map_first_order_lift_residue_field]
  have hc' := hind _ key
  have ht : algebraMap x.A x.Fr x.t ≠ 0 := fun h0 =>
    PowerSeries.X_ne_zero ((IsFractionRing.injective x.A x.Fr) (h0.trans (map_zero _).symm))
  funext i
  have hi := congrFun hc' i
  exact (IsFractionRing.injective x.A x.Fr)
    (((mul_eq_zero.mp hi).resolve_right (pow_ne_zero _ ht)).trans (map_zero _).symm)
