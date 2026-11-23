module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SimilitudesCorrespond
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0219
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Formalism.LocalToGlobal.Columns.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemVGsOfMemQE

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CardLiesOverEqIndex
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm (IsOver PullsBack lowerCoeff levelMapF endF relGroup trivAt)

namespace GlobalTheory.ShFam.Pad

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l l₂ : Level H}

def CxPt (Xo : Moduli Dw l) (c : Coeff l) : Type :=
  {y : Sp ℂ ⟶ Xo.XF c // y ≫ pullback.snd _ _ = spMap c.F.val.toRingHom}

def LiesOver (h : l.Dvd l₂) {Xo : Moduli Dw l} {c : Coeff l} {Xo₂ : Moduli Dw l₂} {c₂ : Coeff l₂}
    (y₂ : CxPt Xo₂ c₂) (y : CxPt Xo c) : Prop :=
  ∃ π : Xo₂.X ⟶ Xo.X, IsOver h Xo Xo₂ π ∧ PullsBack Xo Xo₂ π ∧
    y₂.1 ≫ pullback.fst _ _ ≫ π = y.1 ≫ pullback.fst _ _


open Classical in
def levDeg (h : l.Dvd l₂) (Xo : Moduli Dw l) (c : Coeff l) (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) : ℕ :=
  if k : ∃ n, 0 < n ∧ ∀ y : CxPt Xo c, Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = n then Nat.find k else 1

theorem levDeg_pos (h : l.Dvd l₂) (Xo : Moduli Dw l) (c : Coeff l) (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) :
    0 < levDeg h Xo c Xo₂ c₂ := by
  classical
  unfold levDeg
  split_ifs with k
  · exact (Nat.find_spec k).1
  · exact one_pos

theorem card_lifts_pos {k : Type} [Field k] [IsAlgClosed k] {X Y : Scheme.{0}} (π : X ⟶ Y) [IsFinite π] [Surjective π]
    (y : Sp k ⟶ Y) : 0 < Nat.card {x : Sp k ⟶ X // x ≫ π = y} := by
  have hne : Nonempty {x : Sp k ⟶ X // x ≫ π = y} := by
    have : CompactSpace ↥(pullback π y) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd π y)
    obtain ⟨p, -⟩ := (pullback.snd π y).surjective (default : PrimeSpectrum k)
    obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback π y)) ⟨p, trivial⟩
    refine ⟨pointOfClosedPoint (pullback.snd π y) q hq ≫ pullback.fst π y, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
  have hfin : Finite {x : Sp k ⟶ X // x ≫ π = y} := by
    have hf := (pullback.snd π y).finite_preimage_singleton (IsLocalRing.closedPoint k)
    have := hf.to_subtype
    let s : {x : Sp k ⟶ X // x ≫ π = y} → (Sp k ⟶ pullback π y) := fun x =>
      pullback.lift x.1 (𝟙 _) (x.2.trans (Category.id_comp _).symm)
    refine Finite.of_injective (β := (pullback.snd π y) ⁻¹' {IsLocalRing.closedPoint k})
      (fun x => ⟨s x (IsLocalRing.closedPoint k), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩) fun a b e => ?_
    have e' : s a = s b := ext_of_apply_closedPoint_eq (pullback.snd π y) (pullback.lift_snd _ _ _)
      (pullback.lift_snd _ _ _) (congrArg Subtype.val e)
    exact Subtype.ext ((pullback.lift_fst _ _ _).symm.trans ((congrArg (· ≫ pullback.fst π y) e').trans
      (pullback.lift_fst _ _ _)))
  exact Nat.card_pos

theorem card_liesOver_eq_index (hpq : 1 ≤ Dw.p + Dw.q) (h : l.Dvd l₂) {Xo : Moduli Dw l} {c : Coeff l}
    (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) (y : CxPt Xo c) :
    0 < Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} ∧
      Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = ((trivAt Dw l₂).subgroupOf (relGroup Dw l l₂)).index := by
  obtain ⟨π, hπ, hpb, huniq, ρ, hρ, hone, hmul, -, hρπ, hcov⟩ :=
    (GlobalTheory.LevelCompare.levelMaps_iff hpq).1 (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H Dw hpq).1 l l₂ h Xo Xo₂
  obtain ⟨k₁, -, k₃, k₄⟩ := hcov c₂
  have w : (y.1 ≫ pullback.fst _ _) ≫ Xo.s =
      spMap c₂.F.val.toRingHom ≫ spMap (IntermediateField.inclusion (lowerCoeff h c₂).le).toRingHom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, y.2, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  let y' : Sp ℂ ⟶ Xo.XF (lowerCoeff h c₂) := pullback.lift _ _ w
  have hf : levelMapF h hπ c₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π := pullback.lift_fst _ _ _
  have hs := GlobalTheory.LevelCompare.levelMapF_snd h hπ c₂
  let e : {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} ≃ {x : Sp ℂ ⟶ Xo₂.XF c₂ // x ≫ levelMapF h hπ c₂ = y'} :=
    { toFun := fun a => ⟨a.1.1, by
        obtain ⟨π', a₁, a₂, a₃⟩ := a.2
        obtain rfl := huniq π' a₁ a₂
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, hf, a₃]; exact (pullback.lift_fst _ _ _).symm
        · rw [Category.assoc, hs]; exact a.1.2.trans (pullback.lift_snd _ _ _).symm⟩
      invFun := fun x => ⟨⟨x.1, (congrArg (x.1 ≫ ·) hs.symm).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ pullback.snd _ _) x.2).trans (pullback.lift_snd _ _ _)))⟩, π, hπ, hpb, by
        change x.1 ≫ _ = _
        rw [← hf, ← Category.assoc, x.2]; exact pullback.lift_fst _ _ _⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hpos := card_lifts_pos (levelMapF h hπ c₂) y'
  rw [Nat.card_congr e]
  refine ⟨hpos, ?_⟩
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  have hF : ∀ g, endF (ρ g).hom (hρ g) c₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (ρ g).hom := fun g =>
    pullback.lift_fst _ _ _
  have hS : ∀ g, endF (ρ g).hom (hρ g) c₂ ≫ pullback.snd _ _ = pullback.snd _ _ := fun g => pullback.lift_snd _ _ _
  have hm : ∀ g g', endF (ρ (g * g')).hom (hρ _) c₂ = endF (ρ g).hom (hρ g) c₂ ≫ endF (ρ g').hom (hρ g') c₂ :=
    fun g g' => pullback.hom_ext (by rw [hF, Category.assoc, hF, ← Category.assoc, hF, hmul, Category.assoc]; rfl)
      (by rw [hS, Category.assoc, hS, hS])
  have h1 : endF (ρ 1).hom (hρ _) c₂ = 𝟙 _ :=
    pullback.hom_ext (by rw [hF, hone, Category.id_comp]; exact Category.comp_id _) (by rw [hS, Category.id_comp])
  let f : relGroup Dw l l₂ → {x : Sp ℂ ⟶ Xo₂.XF c₂ // x ≫ levelMapF h hπ c₂ = y'} := fun g =>
    ⟨x ≫ endF (ρ g).hom (hρ g) c₂, by
      rw [← hx, Category.assoc]
      congr 1
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hf, ← Category.assoc, hF, Category.assoc, hρπ]
      · rw [Category.assoc, hs]; exact hS g⟩
  have hsurj : Function.Surjective f := fun a => by
    obtain ⟨g, hg⟩ := (k₄ ℂ x).1 a.1 (a.2.trans hx.symm)
    exact ⟨g, Subtype.ext hg⟩
  have hker : Setoid.ker f = QuotientGroup.rightRel ((trivAt Dw l₂).subgroupOf (relGroup Dw l l₂)) := by
    ext g g'
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, ← (k₄ ℂ x).2, Setoid.ker_def, Subtype.ext_iff, hm]
    change x ≫ _ = x ≫ _ ↔ _
    constructor
    · intro a
      rw [← Category.assoc, ← a, Category.assoc, ← hm, mul_inv_cancel, h1, Category.comp_id]
    · intro a
      have := congrArg (· ≫ endF (ρ g).hom (hρ g) c₂) a
      simp only [Category.assoc] at this
      rw [← hm, inv_mul_cancel, h1, Category.comp_id] at this
      exact this.symm
  rw [← Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hsurj), hker,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)]
  rfl

theorem card_liesOver (hpq : 1 ≤ Dw.p + Dw.q) (h : l.Dvd l₂) {Xo : Moduli Dw l} {c : Coeff l}
    (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) (y : CxPt Xo c) :
    Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = levDeg h Xo c Xo₂ c₂ := by
  classical
  have k : ∃ n, 0 < n ∧ ∀ y : CxPt Xo c, Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = n :=
    ⟨_, (card_liesOver_eq_index hpq h Xo₂ c₂ y).1, fun y' =>
      (card_liesOver_eq_index hpq h Xo₂ c₂ y').2.trans (card_liesOver_eq_index hpq h Xo₂ c₂ y).2.symm⟩
  rw [levDeg, dite_eq_left k]
  exact (Nat.find_spec k).2 y

end GlobalTheory.ShFam.Pad
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
section
noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def IsTw : Prop := ∀ a, I.cst a = twCst I.Ch I.sel (I.tup a) I.glob ∧
  I.idx a = twIdx I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 2)

@[reducible] def canon : TC B X :=
  { I with
    cst := fun a => twCst I.Ch I.sel (I.tup a) I.glob
    idx := fun a => twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2) }

theorem canon_isTw : I.canon.IsTw := fun _ => ⟨rfl, rfl⟩

def Deep : Prop := ∀ a (P : rowSG (B.primes X) I.sel (I.tup a)), P.1 ∉ (B.primes X).vGs → 2 * B.R.m ≤ (I.cst a).D P

variable {I}

theorem IsTw.cst_eq (h : I.IsTw) (a : I.ι) : I.cst a = twCst I.Ch I.sel (I.tup a) I.glob := (h a).1

theorem IsTw.idx_eq (h : I.IsTw) (a : I.ι) :
    I.idx a = twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2) := by
  rw [(h a).2, (h a).1]

theorem IsTw.deep (h : I.IsTw) : I.Deep := fun a P hP => by
  rw [h.cst_eq a, twCst_D_Q hP]

theorem qOf_mod_four (B : Base) (X : PreX B.toPre) : ∀ w ∈ (B.primes X).vGs, qOf w % 4 = 1 := fun w hw => by
  have hPr := (base_fields_primes_ok B X).2.1
  obtain ⟨k, hk⟩ : ∃ k, w ∈ (B.primes X).vG k := by
    classical
    unfold Primes.vGs at hw
    rcases Finset.mem_union.1 hw with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  rw [show qOf w = (B.primes X).g k from hPr.vG_norm k w hk]
  exact (hPr.g_cong k).of_dvd (by
    show 4 ∣ B.host.QS * B.host.q * B.host.d
    exact (((pow_dvd_pow 2 (Nat.le_add_left 2 B.R.e) : 2 ^ 2 ∣ 2 ^ (B.R.e + 2)).trans B.host.tower_dvd).mul_right _).mul_right _)

theorem val_of_ok (h : I.Ok) (j : Fin B.R.m) (w : HeightOneSpectrum (𝓞 B.fields.E)) (hw : w ∈ (B.primes X).vGs) :
    ∃ y : B.fields.K, I.glob.σ₀ y = ((((I.glob.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹ := by
  classical
  have hq : (qOf w : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero w
  have e := (h.idx_ok I.mu0).muqG j j.2 ⟨w, Finset.mem_union_left _ hw⟩ hw (ciQU w) (by simp [ciQU, hq])
  refine ⟨(I.cst I.mu0).muq (j + 1) ⟨w, Finset.mem_union_left _ hw⟩ *
    (qValC (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) w : B.fields.Kˣ), ?_⟩
  rw [map_mul, e, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]

theorem Q_notMem_of_ok (h : I.Ok) (a : I.ι) : ∀ P ∈ I.Q a, P ∉ (B.primes X).vGs := fun _ hP =>
  IdxEx.notMem_vGs_of_mem_QE (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.sel_ok h.g_mem (I.tup a) hP

theorem degOne_of_ok (h : I.Ok) (a : I.ι) (P : rowSG (B.primes X) I.sel (I.tup a)) : TwDegOne B.fields P.1 :=
  degOneUnram_rowSG (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.sel_ok (I.tup a) P

theorem sqrt_of_ok (h : I.Ok) (a : I.ι) (P : rowSG (B.primes X) I.sel (I.tup a)) : ∃ z : B.fields.K, z ^ 2 = (qOf P.1 : B.fields.K) :=
  ⟨_, (h.idx_ok a).cst_ok.sq_sq P⟩

theorem root_of_ok (h : I.Ok) (hD : I.Deep) (a : I.ι) (P : rowSG (B.primes X) I.sel (I.tup a)) (hP : P.1 ∉ (B.primes X).vGs) :
    ∃ z : B.fields.K, I.glob.σ₀ z = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * B.R.m) : ℕ) : ℂ)) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hD a P hP)
  have hq : (qOf P.1 : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
  have hqC : (qOf P.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.cast_ne_zero.1 hq)
  obtain ⟨x1, x2⟩ := (h.idx_ok a).xiUnitAtPrime P
  have hx : I.glob.xi0 ≠ 0 := fun e => x2 (e ▸ redP_zero)
  have hi : IntAt P.1 ((qOf P.1 ^ k : ℕ) : B.fields.E) := by
    simpa using GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P.1 ((qOf P.1 ^ k : ℕ) : ℤ)
  have e := (h.idx_ok a).weil P (I.glob.xi0⁻¹ / (qOf P.1 : B.fields.E) ^ (2 * B.R.m)) ((qOf P.1 ^ k : ℕ) : ℤ)
    (by
      convert hi.mul (yIntAt_inv x1 x2) using 1
      rw [hk]; push_cast; field_simp; ring)
    (by
      convert GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P.1 0 using 1
      rw [hk]; push_cast; field_simp; ring)
  refine ⟨_, e.trans ?_⟩
  congr 1
  rw [hk]; push_cast; field_simp; ring

theorem twIdx_ok_of_ok (h : I.Ok) (hD : I.Deep) (a : I.ι) :
    (twIdx I.Ch I.sel (I.tup a) (twCst I.Ch I.sel (I.tup a) I.glob) (B.R.m - 2)).Ok I.Ch I.sel (I.tup a)
      (twCst I.Ch I.sel (I.tup a) I.glob) I.glob (B.R.m - 2) :=
  twIdx_ok_closed (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.ch_ok (qOf_mod_four B X) I.glob
    h.ch_tied h.weil (val_of_ok h) h.hm (Q_notMem_of_ok h a) (fun P _ => degOne_of_ok h a P) (root_of_ok h hD a)
    (fun P _ => sqrt_of_ok h a P) (fun P _ => (h.idx_ok a).xiUnitAtPrime P)

theorem canon_ok (h : I.Ok) (hD : I.Deep) : I.canon.Ok :=
  { h with sharp := fun _ => rfl, idx_ok := twIdx_ok_of_ok (I := I) h hD }

theorem IsTw.chF_ok (ht : I.IsTw) (h : I.Ok) (W : Wts B.fields (B.primes X).Word B.R) (a : I.ι) (u : (B.primes X).Word) (j : ℕ) :
    (chF W I.sel (I.tup a) (I.idx a) u j).Ok := by
  have ho : ∀ b, ThetaOpen ((I.idx a).levQ j b) := by
    rw [(ht a).2]
    exact thetaOpen_twIdx I.Ch I.sel (I.tup a) (I.cst a) (h.idx_ok a).cst_ok (Q_notMem_of_ok h a) _ j
  exact chF_ok_of_finIdx W I.sel (I.tup a) _ (base_fields_primes_ok B X).1 u j
    (fun b P => thetaOpen_finIdx _ (ho b) P) (fun b c => thetaOpen_root _ (ho b) c)

end GlobalTheory.Mem.Col2.TC

end
end

