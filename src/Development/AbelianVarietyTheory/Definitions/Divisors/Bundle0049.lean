module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)

structure ArchSec (Z : Comp Xo c) (la : Weight Dw) : Type where

  sig : Rul Xo c

  inv : Rul Xo c
  sig_mem : sig ∈ secZ Xo c (exOf Dw la 0)
  inv_mem : inv ∈ secZ Xo c (-exOf Dw la 0)
  idem_sig : idem Z * sig = sig
  idem_inv : idem Z * inv = inv
  mul_inv : sig * inv = idem Z

  cInf : (c.F →+* ℂ) → ℝ
  cInf_pos : ∀ σ, 0 < cInf σ
  norm_inf : ∀ σ, homN (U (goodOf c σ)) x (wtOf Dw la 0) sig '' framesOn (U (goodOf c σ)) Z = {cInf σ}


variable {U x} in
def ArchSec.ofConst {Z : Comp Xo c} {la : Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U x Z la δ) :
    ArchSec U x Z la :=
  ⟨s.sig, s.inv, s.sig_mem, s.inv_mem, s.idem_sig, s.idem_inv, s.mul_inv, s.cInf, s.cInf_pos, s.norm_inf⟩

def Onto : Prop :=
  ∀ σ, GoodEmb c σ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → (∀ τ i, i < Dw.mult τ → 1 ≤ a (τ, i)) →
    4 * (finrank ℚ E * r) + 4 ≤ n →
    holSub0 (U σ).X (laU (U σ) a n) ≤ Submodule.span ℂ (rdU (U σ) '' (cusp Xo c U a n : Set (Rul Xo c)))

structure Laws : Prop where
  pos : 1 ≤ Dw.p + Dw.q
  lev : l.A = 1
  good : ∀ p : ℕ, p.Prime → l.GoodAt p
  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)
  geo : FnAlgClosed (Xo := Xo) (c := c)
  xi : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x
  chi : ∀ σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (laU (U σ) a n k) γ = 1
  det : ∀ σ, GoodEmb c σ → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1
  onto : Onto U
  line : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0

def IsFlatQuot (Z : Comp Xo c) (τ : Psi H) (f g : Rul Xo c) : Prop :=
  ∀ σ, GoodEmb c σ → ∃ a : ℂ, a ≠ 0 ∧ ∀ k (hτ : relab c σ τ.1 ∈ ((U σ).X k).Ψ) y,
    (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
      rdU (U σ) g k y = a * horizGen ⟨_, hτ⟩ y * rdU (U σ) f k y

def Always (Q : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}, (∀ σ : c.F →+* ℂ, Unf Xo c σ r) → ℝ → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → Q U x

def ArchEx : Prop := ∀ (Z : Comp Xo c) (τ : Psi H), Nonempty (ArchSec U x Z (flatWt Dw τ))


def FrameDeg (logOm : ℝ) : Prop :=
  ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ),
    (∀ la, ∀ w ∈ valOn Z la, w s.sig = (ρ la : EReal)) →
      (Function.support ρ).Finite ∧ lineDeg s.cInf ρ = ((Dw.p : ℝ) - Dw.q) / 2 * logOm

def FlatDegreeSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ →
    ∀ (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ),
      Laws U x → FlatDegree U x (CM.logOm E χ).re

end GlobalTheory.FlatCore

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT bc)
open scoped TensorProduct NNReal

namespace GlobalTheory.SphEis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {j m : ℕ}

structure Fr (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E) : Prop where
  cm : IsCMExt F E σ
  herm : IsHermND σ J
  herm₀ : IsHermND σ J₀
  cc : cT (σ : E →+* E) C * J * C = 0
  dd : cT (σ : E →+* E) D * J * D = 0
  cd : cT (σ : E →+* E) C * J * D = 1
  dc : cT (σ : E →+* E) D * J * C = 1
  cz : cT (σ : E →+* E) C * J * Z = 0
  dz : cT (σ : E →+* E) D * J * Z = 0
  zc : cT (σ : E →+* E) Z * J * C = 0
  zd : cT (σ : E →+* E) Z * J * D = 0
  zz : cT (σ : E →+* E) Z * J * Z = J₀
  sum : C * (cT (σ : E →+* E) D * J) + Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + D * (cT (σ : E →+* E) C * J) = 1
  dim : m + 2 * j = n

def fixG {k : ℕ} (C : Matrix (Fin n) (Fin k) E) : Subgroup (GAd σ J) where
  carrier := {g | (matHom _ σ J g).1 * adMat F C = adMat F C}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    change _ * _ = _ at ha hb ⊢
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb, ha]
  inv_mem' := fun {a} ha => by
    change _ * _ = _ at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]

structure IsLv (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E)
    (lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J) : Prop where
  cont : Continuous lv
  onC : ∀ α, (matHom _ σ J (lv α)).1 * adMat F C = adMat F C * α.1
  onD : ∀ α, (matHom _ σ J (lv α)).1 * adMat F D = adMat F D * cT (sigR (AF F) σ) (α⁻¹).1
  onZ : ∀ α, (matHom _ σ J (lv α)).1 * adMat F Z = adMat F Z
  rat : ∀ δ : GL (Fin j) E, lv (bc (inclR (F := F) (AF F)) δ) ∈ ratPts σ J

def plus (J₀ : Matrix (Fin m) (Fin m) E) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) : Matrix (Fin m) (Fin j) (AF F ⊗[F] E) :=
  adMat F J₀⁻¹ * cT (sigR (AF F) σ) b

structure Crd (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E) (u : GAd σ J)
    (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) : Prop where
  onC : (matHom _ σ J u).1 * adMat F C = adMat F C
  onZ : (matHom _ σ J u).1 * adMat F Z = adMat F Z + adMat F C * b
  onD : (matHom _ σ J u).1 * adMat F D = adMat F D - adMat F Z * plus σ J₀ b + adMat F C * c


variable (F E) in
abbrev tor (l : Fin j → ℤ) : GL (Fin j) (AF F ⊗[F] E) := GlobalTheory.Eis.Conv.dg (GlobalTheory.Eis.Conv.halfE F E) l


variable (F) in
abbrev bse : ℝ := 4 ^ Fintype.card (InfinitePlace F)

end GlobalTheory.SphEis

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CM GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames ReciprocityTheory.ChartRestriction.G.Pdiv Formalism.L2.Pj
open scoped CategoryTheory.Obj NNReal

section Index

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


variable (K) in
def detSpan (m : ℕ) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) (⋀[K]^m V) :=
  Submodule.span (𝓞 K) {w | ∃ y : Fin m → V, (∀ i, y i ∈ L) ∧ w = exteriorPower.ιMulti K m y}


variable (K) in
def idx (m : ℕ) (L N : Submodule (𝓞 K) V) : Ideal (𝓞 K) := (detSpan K m N).colon (detSpan K m L)

end Index

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)

def phiP (a : Fin p) : (X.A true).t.G ⟶ X.B.t.G := X.φ (Sum.inl a)

def phiQ (a : Fin q) : (X.A false).t.G ⟶ X.B.t.G := X.φ (Sum.inr a)

def IsGram (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin q) (Fin q) (𝓞 E)) : Prop :=
  (∀ a b, WeilEq X.B.t.PP.L (phiP X a) (phiP X b) (X.A true).t.PP.L ((X.A true).t.act.act (gP a b)) (𝟙 _)
    (spMap (σ₁.comp (algebraMap (𝓞 K) K)))) ∧
  ∀ a b, WeilEq X.B.t.PP.L (phiQ X a) (phiQ X b) (X.A false).t.PP.L ((X.A false).t.act.act (gQ a b)) (𝟙 _)
    (spMap (σ₁.comp (algebraMap (𝓞 K) K)))

variable {X} (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol)
  (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))) (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)))

def IsDiffs : Prop := (∀ a, FP.IsDiffOf FB (phiP X a) (MP a)) ∧ ∀ a, FQ.IsDiffOf FB (phiQ X a) (MQ a)

def subP (τ : 𝓞 E →+* 𝓞 K) : Submodule (𝓞 K) (Fin FB.P₀.g → K) :=
  ⨆ a, (FP.eigLat (X.A true).t.act τ).map ((MP a).restrictScalars (𝓞 K))

def subQ (τ : 𝓞 E →+* 𝓞 K) : Submodule (𝓞 K) (Fin FB.P₀.g → K) :=
  ⨆ a, (FQ.eigLat (X.A false).t.act τ).map ((MQ a).restrictScalars (𝓞 K))

end GlobalTheory.FlatCM

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.ResidueEisenstein

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def ScalesBy (σ : E →ₐ[F] E) {n k : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin k) E) (p : GAd σ J)
    (β : GL (Fin k) (AF F ⊗[F] E)) : Prop := (matHom _ σ J p).1 * adMat F X = adMat F X * β.1

structure DataJ (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) : Prop where
  cm : IsCMExt F E σ
  herm : IsHermND σ J
  witt : IsWittFrame σ J X Y
  lat : Submodule.IsFullLattice E L
  iwa : ∀ g, ∃ p β, ScalesBy σ J X p β ∧ ∃ k ∈ levelAll σ J L a, g = p * k
  ht : ∀ p β, ScalesBy σ J X p β → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det β)

def IsRepsJ (σ : E →ₐ[F] E) {n k : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin k) E) (T : Set (ratPts σ J)) :
    Prop :=
  ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ β, ScalesBy σ J X (γ * t⁻¹ : ratPts σ J).1 β

structure IsFlowJ (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (b : ℝ → GAd σ J) : Prop where
  cont : Continuous b
  add : ∀ s t, b (s + t) = b s * b t
  onX : ∀ t, ∃ β, ScalesBy σ J X (b t) β ∧ (absE F E (Matrix.GeneralLinearGroup.det β) : ℝ) = Real.exp t
  mem : ∀ t, b t ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}
  comm : ∀ t, ∀ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, b t * m = m * b t

end GlobalTheory.ResidueEisenstein

end
end

