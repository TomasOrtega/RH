import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

/- English proof (translation)
Introduce `D i k b b' v v' ρ ρ' Q ψ ψ' ψ₀ ⟨z, hz⟩ hpow hρ hρ'`. Establish `hl` using `(D.ntw.lPrime i).out`. Set `ι : D.ntw.Ok i k →+* FractionRing ρ.Oe` to `(algebraMap ρ.Oe (FractionRing ρ.Oe)).comp (algebraMap _ ρ.Oe)`. Set `ι' : D.ntw.Ok i k →+* FractionRing ρ'.Oe` to `(algebraMap ρ'.Oe (FractionRing ρ'.Oe)).comp (algebraMap _ ρ'.Oe)`. Establish `hι : Function.Injective ι` using `(IsFractionRing.injective ρ.Oe (FractionRing ρ.Oe)).comp ρ.inj`.

Establish `hι' : Function.Injective ι'` using `(IsFractionRing.injective ρ'.Oe (FractionRing ρ'.Oe)).comp ρ'.inj`. Establish `e1 : ∀ g, ι ((ψ (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) = ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL)` using `fun g => (hρ g).symm`. Establish `e1' : ∀ g, ι' ((ψ' (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) = ρ'.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL)` using `fun g => (hρ' g).symm`. Establish `hp : ∀ g, ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) ^ (D.ntw.l i ^ k) = 1` using `fun g => by`. Rewrite using `[← Units.val_pow_eq_pow_val, hpow g, Units.val_one]`.

Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Use `⟨1, by simp, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Take `⟨g, rfl⟩` from `D.ntw.art_surj i Q x`. Establish `h1 : ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = 1` using `by simpa using hp g`.

Establish `h2` using `e1 g`. Establish `h2'` using `e1' g`. Rewrite `h2` using `[h1, map_one, ← map_one ι]`. Rewrite `h2'` using `[h1, map_one, ← map_one ι']`. Rewrite using `[hι' h2', zpow_one, hι h2]`.

Establish `hN : 0 < D.ntw.l i ^ k` using `pow_pos hl.pos k haveI : NeZero (D.ntw.l i ^ k) := ⟨hN.ne'⟩`. Establish `hζ` using `D.ntw.zk_prim i k`. Establish `he : IsPrimitiveRoot (ρ.emb z) (D.ntw.l i ^ k)` using `hz.map_of_injective ρ.emb.injective`. Establish `he' : IsPrimitiveRoot (ρ'.emb z) (D.ntw.l i ^ k)` using `hz.map_of_injective ρ'.emb.injective`. Establish `hζe : IsPrimitiveRoot (ι (D.ntw.zk i k : D.ntw.Ok i k)) (D.ntw.l i ^ k)` using `hζ.map_of_injective hι`.

Establish `hζe' : IsPrimitiveRoot (ι' (D.ntw.zk i k : D.ntw.Ok i k)) (D.ntw.l i ^ k)` using `hζ.map_of_injective hι'`. Take `⟨c, -, hc⟩` from `he.eq_pow_of_pow_eq_one hζe.pow_eq_one`. Take `⟨a, -, ha⟩` from `hζe'.eq_pow_of_pow_eq_one he'.pow_eq_one`. Establish `hcc : c.Coprime (D.ntw.l i ^ k)` using `(he.pow_iff_coprime hN c).1 (hc ▸ hζe)`. Establish `hac : a.Coprime (D.ntw.l i ^ k)` using `(hζe'.pow_iff_coprime hN a).1 (ha ▸ he')`.

Use `⟨((c * a : ℕ) : ℤ), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Int.natAbs_natCast]`. Conclude with `(Nat.Coprime.mul hcc hac).coprime_dvd_right (dvd_pow_self _ hk.ne')`. Use extensionality with `x`. Take `⟨g, rfl⟩` from `D.ntw.art_surj i Q x`.

Take `⟨n, -, hn⟩` from `hz.eq_pow_of_pow_eq_one (hp g)`. Establish `k1 : ι ((ψ (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) ^ (c * a) = ι ((D.ntw.zk i k : D.ntw.Ok i k) ^ (n * a))`. Rewrite using `[e1 g, ← hn, map_pow, map_pow, ← hc, ← pow_mul, ← pow_mul]`. Put the polynomial expressions in normal form. Establish `k2 : ι' ((ψ' (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) = ι' ((D.ntw.zk i k : D.ntw.Ok i k) ^ (n * a))`.

Rewrite using `[e1' g, ← hn, map_pow, map_pow, ← ha, ← pow_mul]`. Put the polynomial expressions in normal form. Rewrite `k1` using `[← map_pow]`. Rewrite using `[hι' k2, zpow_natCast, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hι k1]`.
-/
theorem pulls_eq_zpow : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b b' : Bool) (v v' : D.what₂.places.Pl) (ρ : Reading i k b v) (ρ' : Reading i k b' v') (Q : Finset (PlE D.host)) (ψ ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), (∃ z : D.what₂.LL, IsPrimitiveRoot z (D.ntw.l i ^ k)) → (∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) → ρ.Pulls ψ ψ₀ → ρ'.Pulls ψ' ψ₀ → ∃ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) ∧ ψ' = ψ ^ a := by
  intro D i k b b' v v' ρ ρ' Q ψ ψ' ψ₀ ⟨z, hz⟩ hpow hρ hρ'
  have hl := (D.ntw.lPrime i).out
  let ι : D.ntw.Ok i k →+* FractionRing ρ.Oe := (algebraMap ρ.Oe (FractionRing ρ.Oe)).comp (algebraMap _ ρ.Oe)
  let ι' : D.ntw.Ok i k →+* FractionRing ρ'.Oe := (algebraMap ρ'.Oe (FractionRing ρ'.Oe)).comp (algebraMap _ ρ'.Oe)
  have hι : Function.Injective ι := (IsFractionRing.injective ρ.Oe (FractionRing ρ.Oe)).comp ρ.inj
  have hι' : Function.Injective ι' := (IsFractionRing.injective ρ'.Oe (FractionRing ρ'.Oe)).comp ρ'.inj
  have e1 : ∀ g, ι ((ψ (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) = ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) :=
    fun g => (hρ g).symm
  have e1' : ∀ g, ι' ((ψ' (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) = ρ'.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) :=
    fun g => (hρ' g).symm
  have hp : ∀ g, ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) ^ (D.ntw.l i ^ k) = 1 := fun g => by
    rw [← Units.val_pow_eq_pow_val, hpow g, Units.val_one]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, by simp, ?_⟩
    ext x
    obtain ⟨g, rfl⟩ := D.ntw.art_surj i Q x
    have h1 : ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = 1 := by simpa using hp g
    have h2 := e1 g
    have h2' := e1' g
    rw [h1, map_one, ← map_one ι] at h2
    rw [h1, map_one, ← map_one ι'] at h2'
    rw [hι' h2', zpow_one, hι h2]
  · have hN : 0 < D.ntw.l i ^ k := pow_pos hl.pos k
    haveI : NeZero (D.ntw.l i ^ k) := ⟨hN.ne'⟩
    have hζ := D.ntw.zk_prim i k
    have he : IsPrimitiveRoot (ρ.emb z) (D.ntw.l i ^ k) := hz.map_of_injective ρ.emb.injective
    have he' : IsPrimitiveRoot (ρ'.emb z) (D.ntw.l i ^ k) := hz.map_of_injective ρ'.emb.injective
    have hζe : IsPrimitiveRoot (ι (D.ntw.zk i k : D.ntw.Ok i k)) (D.ntw.l i ^ k) := hζ.map_of_injective hι
    have hζe' : IsPrimitiveRoot (ι' (D.ntw.zk i k : D.ntw.Ok i k)) (D.ntw.l i ^ k) := hζ.map_of_injective hι'
    obtain ⟨c, -, hc⟩ := he.eq_pow_of_pow_eq_one hζe.pow_eq_one
    obtain ⟨a, -, ha⟩ := hζe'.eq_pow_of_pow_eq_one he'.pow_eq_one
    have hcc : c.Coprime (D.ntw.l i ^ k) := (he.pow_iff_coprime hN c).1 (hc ▸ hζe)
    have hac : a.Coprime (D.ntw.l i ^ k) := (hζe'.pow_iff_coprime hN a).1 (ha ▸ he')
    refine ⟨((c * a : ℕ) : ℤ), ?_, ?_⟩
    · rw [Int.natAbs_natCast]
      exact (Nat.Coprime.mul hcc hac).coprime_dvd_right (dvd_pow_self _ hk.ne')
    · ext x
      obtain ⟨g, rfl⟩ := D.ntw.art_surj i Q x
      obtain ⟨n, -, hn⟩ := hz.eq_pow_of_pow_eq_one (hp g)
      have k1 : ι ((ψ (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) ^ (c * a) =
          ι ((D.ntw.zk i k : D.ntw.Ok i k) ^ (n * a)) := by
        rw [e1 g, ← hn, map_pow, map_pow, ← hc, ← pow_mul, ← pow_mul]
        ring_nf
      have k2 : ι' ((ψ' (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) =
          ι' ((D.ntw.zk i k : D.ntw.Ok i k) ^ (n * a)) := by
        rw [e1' g, ← hn, map_pow, map_pow, ← ha, ← pow_mul]
        ring_nf
      rw [← map_pow] at k1
      rw [hι' k2, zpow_natCast, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hι k1]

end GlobalTheory.LevCmp
