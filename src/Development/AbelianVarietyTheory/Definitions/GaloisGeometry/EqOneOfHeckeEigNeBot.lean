module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029

@[expose] public section

noncomputable section

namespace GlobalTheory.W2

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.HodgeCoh

variable {G : GDatum} {gb : GBase G ℂ}

abbrev Z {N : ℕ} (X : GenModel gb N) (k : ℕ) : Scheme.{0} := (GlobalTheory.KS.pow X.univ.A k).left

def zs {N : ℕ} (X : GenModel gb N) (k : ℕ) : Z X k ⟶ Sp ℂ := (GlobalTheory.KS.pow X.univ.A k).hom ≫ X.s

def corrOp {Z Y : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} (c1 c2 : Y ⟶ Z) [IsFinite c1] [Etale c1]
    (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') (a b : ℕ) : hodgeH s a b →ₗ[ℂ] hodgeH s a b :=
  hodgeTrace h1 a b ∘ₗ hodgePull h2 a b

def IsHeckeLift {N k' : ℕ} (X : GenModel gb N) (X' : GenModel gb (N * k')) (g : G.La →ₗ[G.O] G.La) (c : ℕ)
    (π : X'.X ⟶ X.X) (φ : X'.univ.A.left ⟶ X.univ.A.left) : Prop :=
  π ≫ X.s = X'.s ∧ ∃ (o' : GObj gb N X'.s) (ψ : X'.univ.A ⟶ o'.A) (m : GObjMap o' X.univ π),
    IsGHecke g c k' N X'.univ o' ψ ∧ φ = ψ.left ≫ m.φ

def IsHeckeCorr {N : ℕ} (X : GenModel gb N) (k k' : ℕ) (g : G.La →ₗ[G.O] G.La) (c : ℕ)
    (α : Matrix (Fin k) (Fin k) G.O) {Y : Scheme.{0}} (c1 c2 : Y ⟶ Z X k) : Prop :=
  ∃ (X' : GenModel gb (N * k')) (e : Y ≅ Z X' k) (π1 π2 : X'.X ⟶ X.X) (φ1 φ2 : X'.univ.A.left ⟶ X.univ.A.left)
    (h1 : φ1 ≫ X.univ.A.hom = X'.univ.A.hom ≫ π1) (h2 : φ2 ≫ X.univ.A.hom = X'.univ.A.hom ≫ π2),
    IsHeckeLift X X' (k' • LinearMap.id) (k' ^ 2) π1 φ1 ∧ IsHeckeLift X X' g c π2 φ2 ∧
    c1 = e.hom ≫ GlobalTheory.KS.powMap π1 φ1 h1 k ∧
    c2 = e.hom ≫ GlobalTheory.KS.powMap π2 φ2 h2 k ≫ (GlobalTheory.KS.matEnd X.univ.act α).left

def IsHeckeIdx (N : ℕ) (S : Finset ℕ) (g : G.La →ₗ[G.O] G.La) (c : ℕ) : Prop :=
  0 < c ∧ c.Coprime N ∧ (∀ q ∈ S, c.Coprime q) ∧ ∀ x : G.La, ∃ y : G.La, g x - c • x = N • y

def IsHeckeCorrOp {N : ℕ} (X : GenModel gb N) (k k' : ℕ) (g : G.La →ₗ[G.O] G.La) (c a b : ℕ)
    (T : Module.End ℂ (hodgeH (zs X k) a b)) : Prop :=
  ∃ (Y : Scheme.{0}) (c1 c2 : Y ⟶ Z X k) (_ : IsFinite c1) (_ : Etale c1) (h2 : c2 ≫ zs X k = c1 ≫ zs X k),
    IsHeckeCorr X k k' g c 1 c1 c2 ∧ T = corrOp (s := zs X k) (s' := c1 ≫ zs X k) c1 c2 rfl h2 a b

def heckeEig {N : ℕ} (X : GenModel gb N) (k : ℕ) (S : Finset ℕ) (θ : (G.La →ₗ[G.O] G.La) → ℕ → ℂ) (a b : ℕ) :
    Submodule ℂ (hodgeH (zs X k) a b) :=
  ⨅ (g : G.La →ₗ[G.O] G.La) (c : ℕ) (_ : IsHeckeIdx N S g c) (T : Module.End ℂ (hodgeH (zs X k) a b))
    (_ : IsHeckeCorrOp X k c g c a b T), T.maxGenEigenspace (θ g c)

def altPoly {N : ℕ} (X : GenModel gb N) (k : ℕ) (S : Finset ℕ) (θ : (G.La →ₗ[G.O] G.La) → ℕ → ℂ) (d : ℕ) :
    Polynomial ℤ :=
  ∑ a ∈ Finset.range (d + 1), Polynomial.C (∑ b ∈ Finset.range (d + 1),
    (-1 : ℤ) ^ b * (Module.finrank ℂ (heckeEig X k S θ a b) : ℤ)) * Polynomial.X ^ a

section Eig

variable {N : ℕ} {X : GenModel gb N} {k : ℕ} {S : Finset ℕ} {θ : (G.La →ₗ[G.O] G.La) → ℕ → ℂ} {a b : ℕ}

end Eig

end GlobalTheory.W2
