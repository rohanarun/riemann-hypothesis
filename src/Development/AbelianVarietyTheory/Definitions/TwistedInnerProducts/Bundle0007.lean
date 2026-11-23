module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff

namespace GlobalTheory.AscFin

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

def MxOff (P : GlobalTheory.FinPl.Pl D → Prop) {m n : ℕ} (x : Mx D m n) : Prop := ∀ i j, x i j ∈ idOff D P

structure FinLat {m n : ℕ} (A : AddSubgroup (Mx D m n)) : Prop where
  fin : ∀ a ∈ A, MxAt (fun _ => True) a
  cpt : IsCompact (A : Set (Mx D m n))
  opn : ∃ U : Set (Mx D m n), IsOpen U ∧ (0 : Mx D m n) ∈ U ∧ ∀ a ∈ U, MxAt (fun _ => True) a → a ∈ A

structure IsBump {m n : ℕ} (β : Mx D m n → ℂ) : Prop where
  cont : Continuous β
  supp : HasCompactSupport β
  level : ∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → ∀ x, β (x + u) = β x
  smooth : ∀ (k : ℕ) (l : (Fin k → ℝ) →+ Mx D m n), Continuous l → (∀ t, (l t).map (finPart D) = 0) →
    ∀ w, ContDiff ℝ ∞ fun t => β (w + l t)

section Step

variable {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)

structure Pieces (V₀ W W₀ : HSp D) (ρ σ : ℕ) where
  A₁ : AddSubgroup (Mx D W.rank ρ)
  A₂ : AddSubgroup (Mx D W.rank ρ)
  B₁ : AddSubgroup (Mx D σ V₀.rank)
  B₂ : AddSubgroup (Mx D σ V₀.rank)
  Γ₀ : AddSubgroup (WO V₀ W₀)

variable (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ)

structure Pieces.Is (ψ : AddChar (AF D.host.F) ℂ) : Prop where
  a₁ : FinLat p.A₁
  a₂ : FinLat p.A₂
  b₁ : FinLat p.B₁
  b₂ : FinLat p.B₂
  dualA : ∀ a, MxAt (fun _ => True) a → (a ∈ p.A₁ ↔ ∀ a' ∈ p.A₂, ψ (symplO V W (dV.extX W a) (dV.extY W a')) = 1)
  dualA' : ∀ a', MxAt (fun _ => True) a' → (a' ∈ p.A₂ ↔ ∀ a ∈ p.A₁, ψ (symplO V W (dV.extX W a) (dV.extY W a')) = 1)
  dualB : ∀ ξ, MxAt (fun _ => True) ξ → (ξ ∈ p.B₁ ↔ ∀ η ∈ p.B₂, ψ (symplO V₀ W (dW.incX V₀ ξ) (dW.incY V₀ η)) = 1)
  dualB' : ∀ η, MxAt (fun _ => True) η → (η ∈ p.B₂ ↔ ∀ ξ ∈ p.B₁, ψ (symplO V₀ W (dW.incX V₀ ξ) (dW.incY V₀ η)) = 1)
  uni : ∀ u : UX D ρ, MxAt (fun _ => True) (u.1.1 - 1) → x * u.1.1 - x ∈ p.A₁ → psiUni ψ u.1 = 1
  fin₀ : ∀ u ∈ p.Γ₀, MxAt (fun _ => True) (show Mx D W₀.rank V₀.rank from u)
  vac₀ : ∃ f, VacG ψ V₀ W₀ p.Γ₀ f ∧ f ≠ 0

def cls (ψ : AddChar (AF D.host.F) ℂ) : Set (WO V W → ℂ) :=
  {Φ | IsThetaFunO ψ V W Φ ∧ (∀ a ∈ p.A₁, heisO ψ V W (dV.extX W a) Φ = Φ) ∧
    (∀ a ∈ p.A₂, heisO ψ V W (dV.extY W a) Φ = ψ (symplO V W (dV.extX W x) (dV.extY W a)) • Φ) ∧
    (∀ ξ ∈ p.B₁, heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) Φ = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • Φ) ∧
    (∀ η ∈ p.B₂, heisO ψ V W (dV.ext0 W (dW.incY V₀ η)) Φ = Φ) ∧
    IsLatVac (fun w f => heisO ψ V W w f) (p.Γ₀.map ((dV.ext0 W).comp (dW.inc0 V₀))) Φ}

structure Cond (ψ : AddChar (AF D.host.F) ℂ) (P : GlobalTheory.FinPl.Pl D → Prop) (h : GA D W) : Prop where
  pt : ∃ u : UX D ρ, ∃ a ∈ p.A₁, MxOff P (mt W h⁻¹ * (x * u.1.1) - x - a)
  shift : ∀ N : Mx D ρ ρ, MxAt P N → (∀ i j, j ≤ i → N i j = 0) → mt W h⁻¹ * (x * N) ∈ p.A₁ → psiE ψ (upSum N) = 1
  iso : ∀ ξ ∈ p.B₁, ∀ ξ' : Mx D σ V₀.rank, MxAt P ξ → mt W h * dW.incX V₀ ξ = dW.incX V₀ ξ' →
    ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ')) = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ))

def CondK (ψ : AddChar (AF D.host.F) ℂ) (LW : Lat W) (P : GlobalTheory.FinPl.Pl D → Prop) (h : GA D W) : Prop :=
  ∀ κ, InK W LW P κ → Cond dW p x y ψ P (h * κ)

def piecesOf (ψ : AddChar (AF D.host.F) ℂ) (Γ Γ' : AddSubgroup (WO V W)) : Pieces V₀ W W₀ ρ σ where
  A₁ := Γ.comap (dV.extX W)
  A₂ := AddSubgroup.closure {a' | MxAt (fun _ => True) a' ∧
    ∀ a, dV.extX W a ∈ Γ → ψ (symplO V W (dV.extX W a) (dV.extY W a')) = 1}
  B₁ := Γ'.comap ((dV.ext0 W).comp (dW.incX V₀))
  B₂ := Γ'.comap ((dV.ext0 W).comp (dW.incY V₀))
  Γ₀ := Γ.comap ((dV.ext0 W).comp (dW.inc0 V₀))

structure Splits (ψ : AddChar (AF D.host.F) ℂ) (Γ : AddSubgroup (WO V W)) : Prop where
  comp : ∀ u ∈ Γ, ∃ a ∈ p.A₁, ∃ a' ∈ p.A₂, ∃ ξ ∈ p.B₁, ∃ η ∈ p.B₂, ∃ w ∈ p.Γ₀,
    u = dV.extX W a + dV.extY W a' + dV.ext0 W (dW.incX V₀ ξ + dW.incY V₀ η + dW.inc0 V₀ w) ∧
    ψ (symplO V W (dV.extX W x) (dV.extY W a')) = 1 ∧ ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) = 1

structure StdAt (LV : Lat V) (LW : Lat W) (v : GlobalTheory.FinPl.Pl D) : Prop where
  a : ∀ a, MxAt (· = v) a → (a ∈ p.A₁ ↔ dV.extX W a ∈ latO V W (LV : Set _) (LW : Set _) (· = v))
  a' : ∀ a ∈ p.A₁, ∃ b, MxOff (· = v) (a - b) ∧ dV.extX W b ∈ latO V W (LV : Set _) (LW : Set _) (· = v)
  b : ∀ ξ, MxAt (· = v) ξ → (ξ ∈ p.B₁ ↔ dV.ext0 W (dW.incX V₀ ξ) ∈ latO V W (LV : Set _) (LW : Set _) (· = v))

structure GoodAt (ψ : AddChar (AF D.host.F) ℂ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D) : Prop where
  sdV : IsSelfDualC V LV
  sdV₀ : IsSelfDualC V₀ LV₀
  sdW : IsSelfDualC W LW
  sdW₀ : IsSelfDualC W₀ LW₀
  monoV : MonoAt dV LV LV₀ v
  monoW : MonoAt dW LW LW₀ v
  prim : PrimAt ψ dV LV v
  cols : ColsAt dV x LV LW v

end Step

def CosetAt (W : HSp D) (R : Subgroup (GA D W)) (LW : Lat W) (v : GlobalTheory.FinPl.Pl D) (h : GA D W) : Prop :=
  ∃ r ∈ R, r ∈ grpAt W (· = v) ∧ ∃ κ, InK W LW (· = v) κ ∧ h = r * κ

section Stab

variable {S : HSp D} {LS : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}

theorem mulVec_idAt {m n : ℕ} (M : Mx D m n) {z : Fin n → AE D} (hz : ∀ j, z j ∈ idAt D P) (i : Fin m) : (M *ᵥ z) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hz j)

theorem inK_one : InK S LS P 1 := ⟨one_mem _, fun z _ => by rw [mt_one, one_mulVec]⟩

theorem inK_mul {κ κ' : GA D S} (h : InK S LS P κ) (h' : InK S LS P κ') : InK S LS P (κ * κ') :=
  ⟨mul_mem h.1 h'.1, fun z hz => by rw [mt_mul, ← mulVec_mulVec, h'.2 z hz, h.2 _ (mulVec_idAt _ hz)]⟩

theorem inK_inv {κ : GA D S} (h : InK S LS P κ) : InK S LS P κ⁻¹ :=
  ⟨inv_mem h.1, fun z hz => by rw [h.2 _ (mulVec_idAt _ hz), mulVec_mulVec, mt_mul_inv, one_mulVec]⟩

variable {V₀ W W₀ : HSp D} {ρ σ : ℕ} {dW : HypDec W W₀ σ} {p : Pieces V₀ W W₀ ρ σ} {x : Mx D W.rank ρ} {y : Mx D V₀.rank σ}
  {LW : Lat W} {h κ : GA D W}

end Stab

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def idLat {n : ℕ} (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
  Submodule.span (𝓞 D.host.E) {z | ∃ s ∈ I, ∃ y ∈ Λ, z = s • y}


variable (G) in
def shiftId : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  ((G.modul : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) *
    ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹


variable (G) in
def latBig (i : ℕ) : AddSubgroup (WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))) :=
  latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (idLat (shiftId G) (G.Λ (.grid i 0)) : Set _) fun _ => True

def colsOf {n c k : ℕ} (a : Matrix (Fin n) (Fin c) D.host.E) (f : Fin k → Fin c) (s : Fin k → D.host.E) :
    Matrix (Fin n) (Fin k) D.host.E := fun i p => s p * a i (f p)

def IsAuxiliaryVectorWittDec {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ) : Prop :=
  ∃ h : 2 * ρ ≤ c, d.e = colsOf a.a (Fin.castLE (by omega)) (fun p => (-D.host.xi0) ^ (p.1 + 1)) ∧
    ∃ s, d.e' = colsOf a.a (fun p : Fin ρ => (Fin.castLE (by omega) p : Fin c).rev) s

structure Std (F : Frames G) : Prop where
  zA : F.oz.iA = frameMat _ _ G.sp.dec0.ι
  zB : F.oz.iB *ᵥ (show Fin F.Lz.rank → D.host.E from F.ζ 0) = fun i => G.sp.dec0.a i 0
  ζ : ∀ ρ, F.ζ ρ = (-D.host.xi0) ^ ρ • F.ζ 0
  hB : ∀ ρ h, IsAuxiliaryVectorWittDec (G.colDec (2 * ρ + 2) (by omega) h) (F.dB ρ h)
  aB : ∀ ρ h, (F.dB ρ h).i₀ * (F.oB ρ h).iA = frameMat _ _ (G.colDec (2 * ρ + 2) (by omega) h).ι
  zB' : ∀ ρ h, ((F.dB ρ h).i₀ * (F.oB ρ h).iB) *ᵥ F.ζ 0 = fun i => (G.colDec (2 * ρ + 2) (by omega) h).a i ⟨ρ, by omega⟩
  hJ : ∀ ρ h, IsAuxiliaryVectorWittDec (G.colDec (2 * ρ + 1) (by omega) (by omega)) (F.dJ ρ h)
  aJ : ∀ ρ h, (F.dJ ρ h).i₀ = frameMat _ _ (G.colDec (2 * ρ + 1) (by omega) (by omega)).ι

def lat0 (F : Frames G) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) : Lat (F.V₀ ρ) :=
  (G.Λ (.grid (2 * ρ + 2) 0)).comap ((Matrix.mulVecLin (F.dB ρ h).i₀).restrictScalars (𝓞 D.host.E))

def lineLat (F : Frames G) : ∀ ρ, AddSubgroup (WO (G.V (.core (2 * ρ + 1))) (negSp F.Lz))
  | 0 => (latCore G 0).comap ((F.oz.resT _).symm.toAddMonoidHom.comp (AddMonoidHom.inr _ _))
  | σ + 1 => latO _ _ (G.Λ (.core (2 * (σ + 1) + 1)) : Set _)
      (idLat (G.pl.stA sc ^ (σ + 1) * (G.pl.stAbar sc ^ (σ + 1))⁻¹ * shiftId G) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) : Set _)
      fun _ => True

abbrev pcBF (W : G.Weil) (F : Frames G) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) :=
  piecesOf (F.dB ρ h) (F.dJ ρ h) W.ψ (latRow G (2 * ρ + 1)) (latBig G (2 * ρ + 1))

abbrev pcFB (W : G.Weil) (F : Frames G) (σ : ℕ) (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) :=
  piecesOf (F.dJ (σ + 1) h) (F.dB σ h') W.ψ (latRow G (2 * σ + 2)) (latBig G (2 * σ + 2))

abbrev xFB (F : Frames G) (σ : ℕ) (h' : 2 * σ + 2 ≤ D.R.m) := xLast (F.dB σ h') (vecB (F.oB σ h') (F.ζ (σ + 1)))

abbrev yBF (F : Frames G) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) := yZero (F.V₀ ρ) ρ (vecB (F.oB ρ h) (F.ζ (ρ + 1)))

def OnStd (Q : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}, G.Weil → Frames G → Prop) : Prop :=
  All fun {_} _ _ _ {G} W _ => ∀ F : Frames G, Std F → Q W F

end GlobalTheory.AscFin

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsThetaTraceMulTIff
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaTraceTest

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare

attribute [local instance] Over.cartesianMonoidalCategory

theorem fn_ext_of_surjective {W Y : Scheme.{0}} (Ψ : W ⟶ Y) [Surjective Ψ] [IsReduced Y] {U : Y.Opens}
    {a b : Γ(Y, U)} (h : ∀ w, Ψ w ∈ U → gs Ψ w U a = gs Ψ w U b) : a = b := by
  rw [← sub_eq_zero]
  refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => ?_)
  obtain ⟨w, rfl⟩ := Ψ.surjective y
  have hU : Ψ w ∈ U := Y.basicOpen_le _ hy
  have hw : w ∈ W.basicOpen ((Ψ.app U).hom (a - b)) := by
    rw [← Scheme.preimage_basicOpen]; exact hy
  rw [W.mem_basicOpen _ w hU] at hw
  have e := h w hU
  rw [gs_eq _ _ _ hU, gs_eq _ _ _ hU, ← sub_eq_zero, ← map_sub, ← map_sub] at e
  exact absurd (e ▸ hw) not_isUnit_zero

theorem sec_eq_of_surjective {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {T : Over S} {W : Scheme.{0}}
    (Ψ : W ⟶ (T ⊗ A).left) [Surjective Ψ] [IsReduced (T ⊗ A).left] {k : ℤ} {u v : LB.Sec (LPow A L.L k T)}
    (h : ∀ w J, Good L.L w J → sv A L u Ψ w J = sv A L v Ψ w J) : u = v := by
  refine sec_ext fun j => fn_ext_of_surjective Ψ fun w hw => ?_
  obtain ⟨J, hJ, e⟩ := exists_good L.L L.isLB w (fun _ : Fin 1 => Ψ ≫ (snd T A).left) j
    (fun a b _ => by rw [Subsingleton.elim a b]) (fun k => Set.mem_iInter.1 hw k)
  exact (sval_of (L := L.L) (φ := fun _ : Fin 1 => (snd T A).left) u Ψ w J j e).symm.trans
    ((h w J hJ).trans (sval_of (L := L.L) (φ := fun _ : Fin 1 => (snd T A).left) v Ψ w J j e))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

end GlobalTheory.ThetaTraceTest
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Asc

variable {D : D7}


set_option genSizeOfSpec false in
set_option genInjectivity false in
structure Gen (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (Y : Type) [MeasurableSpace Y] where
  d : HypDec V V₀ ρ
  χV : (AE D)ˣ →* Circle
  χW : (AE D)ˣ →* Circle
  om : Om V W
  vS : VolM D W.rank ρ
  vN : VolN d
  vb : VolM D ρ V₀.rank
  vU : VolU D ρ
  vW : GlobalTheory.Unf.Vol W
  x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E
  m : Measure Y
  g : Y → GA D V₀
  Th : Y → GA D V → ℂ

namespace Gen

variable {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y]
  (a : Gen ψ V V₀ W ρ Y)

structure Is : Prop where
  weil : IsWeilDatumO ψ V W a.χV a.χW a.om
  base : IsBase W a.x₀
  sfin : SFinite a.m
  g : Continuous a.g
  th : ∀ y, IsTh ψ a.d W a.x₀ (a.Th y)
  cont : Continuous fun p : Y × flagN a.d => a.Th p.1 p.2.1
  small : ∃ M : Y → ℝ, Measurable M ∧ (∀ y, ∀ n ∈ flagN a.d, ‖a.Th y n‖ ≤ M y) ∧
    ∀ k : ℕ, Integrable (fun y => M y * quotHeight V₀ (a.g y) ^ k) a.m

def lhs (G : GA D W → ℂ) (Φ : WO V W → ℂ) : ℂ :=
  ∫ y, (∫ n in a.vN.𝓝, a.Th y n.1 * liftS a.om a.vW.μ a.vW.𝓕 G Φ (n.1 * a.d.emb0 (a.g y)) ∂a.vN.ν) ∂a.m

def ker (G : GA D W → ℂ) (Φ : WO V W → ℂ) (h : GA D W) : ℂ :=
  G h * ∫ y, fl ψ a.d W a.vS a.vb a.vU (a.Th y) (rat a.x₀) (a.om (a.d.emb0 (a.g y), h) Φ) ∂a.m

def tot (G : GA D W → ℂ) (Φ : WO V W → ℂ) (p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank) : ℂ :=
  G p.1.1 * flFun ψ a.d W a.vS (a.Th p.1.2) (rat a.x₀) (a.om (a.d.emb0 (a.g p.1.2), p.1.1) Φ) p.2.1 p.2.2

def totMeas (𝓑 : Set (GA D W)) : Measure ((GA D W × Y) × UX D ρ × Mx D ρ V₀.rank) :=
  ((a.vW.μ.restrict 𝓑).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))

end Gen

def strip (W : HSp D) (R : Subgroup (GA D W)) (C : Set (GA D W)) : Set (GA D W) := {h | ∃ r ∈ R, ∃ c ∈ C, ∃ b ∈ GfC W, h = r * c * b}

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) (v : CoreVol G) (F : Frames G)
  (Ψ : ∀ i, Fn G (.core i)) (u : GA D (Yc D 0) → ℂ)

def NZJ (ΓL : ∀ ρ, AddSubgroup (WO (G.V (.core (2 * ρ + 1))) (negSp F.Lz))) (k : ℕ) (h : 2 * k + 2 ≤ D.R.m) : Prop :=
  ∃ (χ' : (AE D)ˣ →* Circle) (omz : Om (G.V (.core (2 * k + 1))) (negSp F.Lz)), IsWeilDatumO W.ψ _ _ χ' L.eta omz ∧
    ∃ ρ Φ Φ₀, VacG W.ψ _ _ (ΓL k) Φ₀ ∧
      (F.jac v k h).per W.ψ (F.ζ k) omz (star (Ψ (2 * k + 1))) (star (part W M ρ Φ u (2 * k + 1) (by omega))) Φ₀ ≠ 0

def NZB (k : ℕ) (h : 2 * k + 2 ≤ D.R.m) : Prop :=
  ∃ ρ Φ, (F.bes v k h).per W.ψ (star (Ψ (2 * k + 2))) (star (part W M ρ Φ u (2 * k + 2) h)) ≠ 0

def OnTower (Q : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (_ : G.Weil) (_ : GlobalTheory.FunObj.Vol G) (_ : CoreVol G)
    (F : Frames G) (_ : ∀ i, Fn G (.core i)) (_ : GA D (Yc D 0) → ℂ) (_ : ∀ ρ, AddSubgroup (WO (G.V (.core (2 * ρ + 1))) (negSp F.Lz))), Prop) :
    Prop :=
  All fun {_} _ _ _ {G} W M => ∀ (v : CoreVol G) (F : Frames G) ΓL, F.Ends v W M → F.Good v W ΓL → ∀ Ψ, IsColChain W v Ψ →
    ∀ u, RapidRow W M u → Q W M v F Ψ u ΓL

def Rung0 : Prop := OnTower fun {_} _ _ _ {G} W M v F Ψ u ΓL => per0 G M (Ψ 0) u ≠ 0 → ∀ h, NZJ W M v F Ψ u ΓL 0 h

def RungB : Prop := OnTower fun {_} _ _ _ _ W M v F Ψ u ΓL => ∀ k h, NZJ W M v F Ψ u ΓL k h → NZB W M v F Ψ u k h

def RungJ : Prop := OnTower fun {_} _ _ _ _ W M v F Ψ u ΓL => ∀ k h h', NZB W M v F Ψ u k h' → NZJ W M v F Ψ u ΓL (k + 1) h

def ConjRead : Prop := All fun {D} _ {L} _ {G} W M => ∀ i, ∀ hi : i < D.R.m,
  IsWeilDatumO W.ψ _ _ (G.chrS (.chi i 0))⁻¹ (G.chrT (.chi i 0))⁻¹ (omRow W i) ∧
  IsWeilDatumO W.ψ _ _ (G.ch.chi (D.R.m - i))⁻¹ (G.ch.chi (D.R.m - i))⁻¹ (omCore W i) ∧
  (Odd i → (G.chrS (.chi i 0))⁻¹ = (G.ch.chi (D.R.m - i))⁻¹ * L.eta ∧ G.chrT (.chi i 0) = G.ch.chi (D.R.m - i)) ∧
  (Even i → (G.chrT (.chi i 0))⁻¹ = (G.ch.chi (D.R.m - i))⁻¹ * L.eta ∧ G.chrS (.chi i 0) = G.ch.chi (D.R.m - i)) ∧
  (∀ f, Dep W (.core i) f ↔ VacG W.ψ _ _ (latCore G i) (star f)) ∧
  (∀ (v : CoreVol G) f Ψ, star (dn W v i f Ψ) = liftT (omCore W i) (v (i + 1)).μ (v (i + 1)).𝓕 (star Ψ) (star f)) ∧
  (∀ ρ Φ u, star (part W M ρ Φ u (i + 1) hi) =
    liftS (omRow W i) (M.ν (.grid i 0)) (M.fd (.grid i 0)) (star (part W M ρ Φ u i hi.le)) (star (W.datum ρ Φ ⟨i, hi⟩))) ∧
  (∀ ρ Φ ρ' Φ' u, (∀ j : Fin D.R.m, j.1 < i → ρ j = ρ' j ∧ Φ j = Φ' j) → part W M ρ Φ u i hi.le = part W M ρ' Φ' u i hi.le) ∧
  (M.ν (.grid i 0)).IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.V (.grid i 0))) (M.fd (.grid i 0)) (M.ν (.grid i 0))

def PartFixed : Prop := All fun {_} _ _ _ {G} W M => ∀ ρ Φ u i h, ∀ k ∈ lev G (.grid (i + 1) 0), ∀ g,
  part W M ρ Φ u (i + 1) h (g * k) = part W M ρ Φ u (i + 1) h g

end GlobalTheory.Asc

end
end

