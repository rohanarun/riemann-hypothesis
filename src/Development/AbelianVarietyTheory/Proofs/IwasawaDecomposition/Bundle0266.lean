module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0749
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvSmulMemOfRedL
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Lean

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
section
noncomputable section

namespace GlobalTheory.Mem.Col2.StepZero

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.HLatOps
open scoped ComplexOrder

section Metric

variable {K : Type} [Field K] [NumberField K] [StarRing K] (C : CSD K)

@[reducible] def valDatum : GSD K where
  G := Unit
  D := Unit
  V := C.V
  ιV := C.ιV
  bV := C.bV
  pair := C.pair
  ρ := 1
  Nab _ := ⊥
  Del _ := ⊥

theorem majAt_eq_classSum (hb : C.HasRatBasis) (hp : ∀ v : InfinitePlace K, (C.H.map v.embedding).PosDef)
    (v : InfinitePlace K) (x y : C.Forms) :
    Formalism.HermitianLatticesTheory.majAt C.basis (stdFrame C.H) v x y =
      ∑ c, ((C.wt c : ℕ) : ℂ)⁻¹ * (valDatum C).pairAt v (x.1 c) (y.1 c) := by
  have hs : IsSesq (fun v (x y : C.Forms) => ∑ c, ((C.wt c : ℕ) : ℂ)⁻¹ * (valDatum C).pairAt v (x.1 c) (y.1 c)) := by
    intro v
    refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← mul_add, ← GSD.pairAt_add_left]
      rfl
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← mul_add, ← GSD.pairAt_add_right]
      rfl
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [mul_left_comm, ← GSD.pairAt_smul_left]
      rfl
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [mul_left_comm, ← GSD.pairAt_smul_right]
      rfl
  have hg : gramOf C.basis (fun (x y : C.Forms) => ∑ c, ((C.wt c : ℕ) : ℂ)⁻¹ * (valDatum C).pairAt v (x.1 c) (y.1 c)) =
      C.H.map v.embedding := by
    ext a a'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gramOf, Matrix.of_apply, Matrix.map_apply, CSD.H, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    exact ((valDatum C).pairAt_of_rat v _ _ fun i => C.basis_rat hb a c i).symm
  rw [sesq_eq_sum (isSesq_maj C.basis (stdFrame C.H)) C.basis v x y, sesq_eq_sum hs C.basis v x y, gramOf_maj, hg]
  have := (frameOfSpec _ _ (hp v)).2
  unfold metOf at this
  unfold stdFrame
  rw [this]

end Metric

section Forget

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
  (pref : DecoF X.E n ST SG Q → Prop) (lam : X.Tau → DomWeight n) {Λ₀ : LevFam X.E X.K n SG}


variable (ST Λ₀) in
abbrev base : GSD X.K := formGSD (roundPk X lam fun d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) => d.1.Lsh) Λ₀

def down (hΛ : ∀ b, Λ b = Λ₀) (b : β) : (stepY ST y β Λ Θ pref).G b →* FormG Λ₀ where
  toFun g := (g.1, ⟨g.2.1.1, hΛ b ▸ g.2.1.2⟩)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem deco_smul (hΛ : ∀ b, Λ b = Λ₀) (b : β) (g : (stepY ST y β Λ Θ pref).G b) (p : (stepY ST y β Λ Θ pref).D b) :
    (g • p).1.1.deco = down pref hΛ b g • p.1.1.deco := rfl

theorem chr_eq_one {Θ' : LevQFam X.E X.K n Q} (h : Θ' = LevQFam.top X.E X.K n Q) (c : Θ'.grp) : Θ'.chr c = 1 := by
  subst h
  exact LevQFam.top_chr c

theorem mem_grp {Θ' : LevQFam X.E X.K n Q} (h : Θ' = LevQFam.top X.E X.K n Q) (c : GLQ X.E n Q) : c ∈ Θ'.grp := by
  subst h
  exact (Subgroup.mem_pi _).2 fun _ _ => Subgroup.mem_top _

theorem chr_congr {Λ' : LevFam X.E X.K n SG} (h : Λ' = Λ₀) (a : Λ'.grp) : Λ'.chr a = Λ₀.chr ⟨a.1, h ▸ a.2⟩ := by
  subst h
  rfl

theorem rho_eq (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (b : β) (g : (stepY ST y β Λ Θ pref).G b) :
    (stepY ST y β Λ Θ pref).rho X.emb lam b g = (base ST lam Λ₀).ρ (down pref hΛ b g) := by
  have h : (stepY ST y β Λ Θ pref).chr b g = Λ₀.chr (down pref hΛ b g).2 := by
    show (Λ b).chr g.2.1 * (Θ b).chr g.2.2 = _
    rw [chr_eq_one (hΘ b), mul_one, chr_congr (hΛ b)]
    rfl
  show (((stepY ST y β Λ Θ pref).chr b g : X.Kˣ) : X.K) • rhoVr X.emb lam ((stepY ST y β Λ Θ pref).gam b g) = _
  rw [h]
  rfl

theorem form_smul (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (φ : (base ST lam Λ₀).EqFun) (b : β)
    (g : (stepY ST y β Λ Θ pref).G b) (p : (stepY ST y β Λ Θ pref).D b) :
    φ.1 (g • p).1.1.deco = (stepY ST y β Λ Θ pref).rho X.emb lam b g (φ.1 p.1.1.deco) := by
  rw [rho_eq pref lam hΛ hΘ]
  exact φ.2 (down pref hΛ b g) p.1.1.deco

theorem pt_ext (hy : ∀ N, y.ys N = {∅}) {p q : PtY ST SG Q y} (h : p.1.1 = q.1.1) : p = q := by
  have h1 := p.2
  have h2 := q.2
  rw [hy, Set.mem_singleton_iff] at h1 h2
  exact Subtype.ext (Prod.ext h (h1.trans h2.symm))

theorem exists_lift (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (b : β)
    (p q : (stepY ST y β Λ Θ pref).D b) (g₀ : FormG Λ₀) (h : g₀ • p.1.1.deco = q.1.1.deco) :
    ∃ g : (stepY ST y β Λ Θ pref).G b, down pref hΛ b g = g₀ ∧ g • p = q := by
  obtain ⟨c, hc⟩ := GlobalTheory.FramedForms.exists_smul_of_deco_eq
    (p := ((g₀.1, g₀.2.1, 1) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • p.1.1) (q := q.1.1) h
  refine ⟨(g₀.1, ⟨g₀.2.1, (hΛ b).symm ▸ g₀.2.2⟩, ⟨c, mem_grp (hΘ b) c⟩), rfl, pt_ext hy ?_⟩
  rw [hc, smul_smul]
  simp only [Prod.mk_mul_mk, one_mul, mul_one]
  rfl

theorem exists_pt (hy : ∀ N, y.ys N = {∅}) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : ∃ p : PtY ST SG Q y, p.1.1.deco = d := by
  obtain ⟨γ, -, hγ⟩ := GlobalTheory.SemilocalBasis.exists_equiv X.E n Q d.1.N
    { toIsLattice := d.2.lat
      span_eq_top := GlobalTheory.LvT.Pts.span_eq_top_of_unimodular d.1.N d.2.lat d.2.uni }
  exact ⟨⟨(⟨(d, fun _ => γ), fun P x => hγ P.1 P.2 x⟩, ∅), by rw [hy]; rfl⟩, rfl⟩

theorem card_stab (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (b : β)
    (p : (stepY ST y β Λ Θ pref).D b) :
    Nat.card (MulAction.stabilizer ((stepY ST y β Λ Θ pref).G b) p) =
      Nat.card (MulAction.stabilizer (FormG Λ₀) p.1.1.deco) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun g => ⟨down pref hΛ b g.1, (deco_smul pref hΛ b g.1 p).symm.trans (congrArg (fun q => q.1.1.deco) g.2)⟩) ⟨?_, ?_⟩)
  · intro g g' h
    have h1 : g.1.1 = g'.1.1 := congrArg (fun a => a.1.1) h
    have h2 : (g.1⁻¹ * g'.1) = 1 := stepY_eq_one y β Λ Θ pref b _ p (g⁻¹ * g').2 (by
      show g.1.1⁻¹ * g'.1.1 = 1
      rw [h1, inv_mul_cancel])
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  · intro g₀
    obtain ⟨g, h1, h2⟩ := exists_lift pref hy hΛ hΘ b p p g₀.1 g₀.2
    exact ⟨⟨g, h2⟩, Subtype.ext h1⟩

def clMap (c : (stepY ST y β Λ Θ pref).Cl) : (base ST lam Λ₀).Cl :=
  (base ST lam Λ₀).cls ((stepY ST y β Λ Θ pref).rep c).1.1.deco

theorem clMap_cl (hΛ : ∀ b, Λ b = Λ₀) (b : β) (p : (stepY ST y β Λ Θ pref).D b) :
    clMap (Λ₀ := Λ₀) pref lam ((stepY ST y β Λ Θ pref).cl b p) = (base ST lam Λ₀).cls p.1.1.deco := by
  conv_rhs => rw [← (stepY ST y β Λ Θ pref).mv_smul b p, deco_smul pref hΛ]
  exact ((base ST lam Λ₀).cls_smul _ _).symm

theorem clMap_bijective [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    Function.Bijective (clMap (y := y) (Λ := Λ) (Θ := Θ) (Λ₀ := Λ₀) pref lam) := by
  refine ⟨?_, fun c₀ => ?_⟩
  · rintro ⟨b, q⟩ ⟨b', q'⟩ h
    obtain rfl : b = b' := Subsingleton.elim _ _
    obtain ⟨g₀, hg⟩ := ((base ST lam Λ₀).cls_eq_iff _ _).1 h
    obtain ⟨g, -, h2⟩ := exists_lift pref hy hΛ hΘ b _ _ g₀ hg
    congr 1
    rw [← (stepY ST y β Λ Θ pref).rp_spec b q, ← (stepY ST y β Λ Θ pref).rp_spec b q']
    exact Quotient.sound ⟨g, h2⟩
  · induction c₀ using Quotient.inductionOn' with
    | h d =>
      obtain ⟨p, rfl⟩ := exists_pt (Q := Q) hy d
      exact ⟨(stepY ST y β Λ Θ pref).cl default p, clMap_cl pref lam hΛ default p⟩

def clEquiv [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    (stepY ST y β Λ Θ pref).Cl ≃ (base ST lam Λ₀).Cl :=
  Equiv.ofBijective _ (clMap_bijective pref lam hy hΛ hΘ)

end Forget

section Zero

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ} (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word)

theorem m_pos (R : Ranks) : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m

variable (sel mu cst) in
theorem ysAt_zero (N : Submodule (𝓞 X.E) (Sp X.E (R.N 0))) : (ysAt R sel mu cst 0).ys N = {∅} := by
  have h : ¬ (0 + 1 = R.m) := by have := R.two_le_m; omega
  unfold ysAt
  rw [if_neg h]
  rfl

@[reducible] def idxUnique (hL : L.Ok Ch sel mu cst G m2) : Unique (Idx sel mu L 0) where
  default := ⟨some hL.zero_uniq.choose, by simpa using m_pos R⟩
  uniq := by
    rintro ⟨_ | b, hb⟩
    · exact absurd (hb.2 (m_pos R)) (by simp)
    · exact Subtype.ext (congrArg some (hL.zero_uniq.choose_spec b))

theorem levGAt_zero (hL : L.Ok Ch sel mu cst G m2) (b : Idx sel mu L 0) : levGAt sel mu L Tp 0 b = colLev Ch 0 := by
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 (m_pos R)) (by simp)
  · exact hL.zero_G b

theorem levQAt_zero (hL : L.Ok Ch sel mu cst G m2) (b : Idx sel mu L 0) :
    levQAt sel mu L Tp 0 b = LevQFam.top X.E X.K (R.N 0) _ := by
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 (m_pos R)) (by simp)
  · exact hL.zero_Q b

variable (hX : X.Ok) (hL : L.Ok Ch sel mu cst G m2) (h : ((stepAt sel mu cst L Tp u 0).fam X.emb (lamT (W.hc u) 0)).Ok)

variable (rho : ∀ i (b : Idx sel mu L i), (stepAt sel mu cst L Tp u i).D b → ℂ)
  (rho' : ∀ i (b : Idx sel mu L (i + 1)), (stepAt sel mu cst L Tp u (i + 1)).D b → ℂ) (cD : X.Tau → ℂ)
  (Th : ∀ i (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)), (stepAt sel mu cst L Tp u i).D b →
    (stepAt sel mu cst L Tp u (i + 1)).D b' → Formalism.L2.Ker.VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ)
  (xi0 : X.E) (du : ℕ) (Ds Gp : ℝ) (σ : X.K →+* ℂ)

theorem embF_injective {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (T : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (h : (T.fam emb lam).Ok) :
    Function.Injective (T.embF emb σ lam h) :=
  inj_of_li σ _ (T.hlat emb lam h).b (T.lawBasis_of_ok emb σ lam h).1

theorem embF_mem_Fi {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (T : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (h : (T.fam emb lam).Ok)
    (x : T.FormsK emb lam h) : T.embF emb σ lam h x ∈ T.Fi emb σ lam := by
  rw [← (T.lawBasis_of_ok emb σ lam h).2]
  exact mem_span_basis_image σ (T.hlat emb lam h).b _ x

end Zero

end GlobalTheory.Mem.Col2.StepZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfBearCommonFullFlag
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

theorem GlobalTheory.FlagBundle.eq_of_coBear : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (K : Type) [Field K] (p p' : Sp K ⟶ Y₁.X) (q : Sp K ⟶ Y₂.X), p ≫ f₁ = q ≫ f₂ → p' ≫ f₁ = q ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p q → CoBear Eb S₁ φ₁ S₂ φ₂ (p' ≫ f₁) p' q → p = p' := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ K _ p p' q hp hp' hc hc'
  obtain ⟨A, hA, h, hh, hAp, hAq⟩ := hc
  obtain ⟨B, hB, h', -, hBp', hBq⟩ := hc'
  have hA' : A ∈ Eb.S ((q ≫ f₂) (IsLocalRing.closedPoint K)) := hp ▸ hA
  have hB' : B ∈ Eb.S ((q ≫ f₂) (IsLocalRing.closedPoint K)) := hp' ▸ hB
  have hAp' : Bears S₁ φ₁ A h p' :=
    _root_.GlobalTheory.FlagBundle.Bears.transfer F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ hR₂ hR₁ K q p' hp'.symm A hA' B hB' h h' hAq hBq hBp'
  exact (hR₁.2.2 K (p ≫ f₁) A hA h hh).unique ⟨rfl, hAp⟩ ⟨hp'.trans hp.symm, hAp'⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdmissibleLocalComponentDefiniteUnitary
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.LocAdm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_finGL : Continuous (finGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact (continuous_const.add (continuous_id.matrix_map hs) :
    Continuous fun x : Matrix (Fin n) (Fin n) (Af E) => 1 - matN n (sFin E) 1 + x.map (sFin E))

theorem t2Space_finiteAdeleRing_cmField : T2Space (FiniteAdeleRing (𝓞 E) E) :=
  inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))

theorem t2Space_adeleRing_cmField : T2Space (Ad E) :=
  haveI := t2Space_finiteAdeleRing_cmField (E := E)
  haveI : T2Space (InfiniteAdeleRing E) := inferInstanceAs (T2Space ((v : InfinitePlace E) → v.Completion))
  inferInstanceAs (T2Space (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))

theorem t2Space_adelicGL_cmField : T2Space (GA E n) :=
  haveI := t2Space_adeleRing_cmField (E := E)
  Units.isEmbedding_embedProduct.t2Space

theorem isClosed_UA : IsClosed ((UA E n : Subgroup (GA E n)) : Set (GA E n)) := by
  haveI := t2Space_adeleRing_cmField (E := E)
  show IsClosed {g : GA E n | ((g : Matrix (Fin n) (Fin n) (Ad E)).map (conjAd E))ᵀ * 1 * (g : Matrix (Fin n) (Fin n) (Ad E)) = 1}
  exact isClosed_eq (((Units.continuous_val.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose.matrix_mul
    continuous_const).matrix_mul Units.continuous_val) continuous_const

theorem locU_le_finU (w : HeightOneSpectrum (𝓞 E)) : locU n w ≤ finU (E := E) (n := n) := inf_le_left

theorem continuous_inclusion_locU (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (Subgroup.inclusion (locU_le_finU (n := n) w)) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem isClosed_of_retract (w : HeightOneSpectrum (𝓞 E)) (r : UA E n →* locU n w) (hr : Continuous r)
    (hx : ∀ x : locU n w, r x = x) : IsClosed ((locU n w : Subgroup (UA E n)) : Set (UA E n)) := by
  haveI := t2Space_adelicGL_cmField (E := E) (n := n)
  have e : ((locU n w : Subgroup (UA E n)) : Set (UA E n)) = {x | ((r x : locU n w) : UA E n) = x} := by
    ext x
    constructor
    · intro h
      exact congrArg Subtype.val (hx ⟨x, h⟩)
    · intro h
      change x ∈ locU n w
      rw [← show ((r x : locU n w) : UA E n) = x from h]
      exact (r x).2

  rw [e]
  exact isClosed_eq (continuous_subtype_val.comp hr) continuous_id

theorem isSmooth_loc (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)) :
    IsSmooth (π.rep.comp (locU n w).subtype) := fun v => by
  have h := (π.isAut.aut v.1 v.2).level
  convert h.preimage (continuous_inclusion_locU (n := n) w) using 1
  ext k
  exact Subtype.ext_iff

theorem exists_compact_open (w : HeightOneSpectrum (𝓞 E)) (r : UA E n →* locU n w) (hr : Continuous r)
    (hx : ∀ x : locU n w, r x = x) (L : Subgroup (finU (E := E) (n := n))) (hL : IsOpen (L : Set (finU (E := E) (n := n)))) :
    ∃ K : Subgroup (locU n w), IsOpen (K : Set (locU n w)) ∧ IsCompact (K : Set (locU n w)) ∧
      K ≤ L.comap (Subgroup.inclusion (locU_le_finU w)) := by
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E n
  let p : locU n w →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (locU n w).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  let K : Subgroup (locU n w) := U0.comap p ⊓ L.comap (Subgroup.inclusion (locU_le_finU w))
  have hKo : IsOpen (K : Set (locU n w)) :=
    (hU0o.preimage hp).inter (hL.preimage (continuous_inclusion_locU w))
  have hι : Topology.IsClosedEmbedding (fun x : locU n w => ((x : UA E n) : GA E n)) :=
    isClosed_UA.isClosedEmbedding_subtypeVal.comp (isClosed_of_retract w r hr hx).isClosedEmbedding_subtypeVal
  refine ⟨K, hKo, IsCompact.of_isClosed_subset (hι.isCompact_preimage (hU0c.image continuous_finGL))
    (Subgroup.isClosed_of_isOpen K hKo) fun x hx => ⟨p x, (Subgroup.mem_inf.1 hx).1, ?_⟩, inf_le_right⟩
  have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := (Subgroup.mem_inf.1 x.2).1
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

theorem exists_admissible_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n)
    (w : HeightOneSpectrum (𝓞 E)), ∃ σ : SmIrr (locU n w), IsAdmissible σ.ρ ∧
      IsCompAlong π.V (locU n w) (MonoidHom.id _) σ.ρ := by
  intro E _ _ _ n π w
  obtain ⟨r, hr, hrx, hrc⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  have hadm := (GlobalTheory.T.definiteUnitary_admissible_finiteMultiplicity E n π).1
  let ρ : Representation ℂ (locU n w) π.V := π.rep.comp (locU n w).subtype
  let ρf : Representation ℂ (finU (E := E) (n := n)) π.V := π.rep.comp (finU (E := E) (n := n)).subtype
  have hρ : IsSmooth ρ := isSmooth_loc π w
  have hle := locU_le_finU (n := n) w
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.isAut.ne_bot
  let v0 : π.V := ⟨φ, hφ⟩
  have hv0 : v0 ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  let L : Subgroup (finU (E := E) (n := n)) := LocEx.stab ρf v0
  have hLo : IsOpen (L : Set (finU (E := E) (n := n))) := by
    convert (π.isAut.aut φ hφ).level using 1
    ext k
    exact Subtype.ext_iff
  have hLl : IsOpen ((L.comap (Subgroup.inclusion hle) : Subgroup (locU n w)) : Set (locU n w)) :=
    hLo.preimage (continuous_inclusion_locU w)
  obtain ⟨K, hKo, hKc, hKL⟩ := exists_compact_open w r hr hrx L hLo

  have hT : ∀ x : UA E n, ∀ (g : locU n w) (y : π.V),
      π.rep ((r x : UA E n)⁻¹ * x) (ρ g y) = ρ g (π.rep ((r x : UA E n)⁻¹ * x) y) := fun x g y => by
    change π.rep _ (π.rep (g : UA E n) y) = π.rep (g : UA E n) (π.rep _ y)
    rw [← Module.End.mul_apply, ← map_mul, (hrc x g).eq, map_mul, Module.End.mul_apply]
  have hst : ∀ x, ∀ y ∈ LocEx.nullPart ρ K, π.rep x y ∈ LocEx.nullPart ρ K := fun x y hy => by
    have h1 := LocEx.nullPart_act ρ K (r x) (LocEx.nullPart_comm ρ K (π.rep ((r x : UA E n)⁻¹ * x)) (hT x) hy)
    have e : π.rep x y = ρ (r x) (π.rep ((r x : UA E n)⁻¹ * x) y) := by
      change _ = π.rep (r x : UA E n) _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    rw [e]
    exact h1
  have hφK : v0 ∈ fixed ρ K := LocEx.mem_fix.2 fun k hk => hKL hk
  have h2 : ∀ W : Submodule ℂ π.V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W ⊓ fixed ρ K = ⊥ → W = ⊥ := by
    intro W hW h
    rcases ((CuspRep.isIrreducible_iff _).1 π.isIrreducible_rep).2 (LocEx.nullPart ρ K) hst with h1 | h1
    · exact le_bot_iff.1 (h1 ▸ LocEx.le_nullPart hρ hKc W hW h)
    · exact absurd (LocEx.eq_zero_of_mem_nullPart hρ hKc hφK (h1 ▸ Submodule.mem_top)) hv0

  let M : Subgroup (UA E n) := L.map (finU (E := E) (n := n)).subtype ⊓ r.ker
  have hcomm : ∀ k ∈ M, ∀ g : locU n w, Commute k (g : UA E n) := fun k hk g => by
    have h := hrc k g
    rwa [MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hk).2, OneMemClass.coe_one, inv_one, one_mul] at h
  have hU : ∀ g, ∀ v ∈ fixed π.rep M, ρ g v ∈ fixed π.rep M := fun g v hv => LocEx.mem_fix.2 fun k hk => by
    change π.rep k (π.rep (g : UA E n) v) = π.rep (g : UA E n) v
    rw [← Module.End.mul_apply, ← map_mul, (hcomm k hk g).eq, map_mul, Module.End.mul_apply,
      LocEx.mem_fix.1 hv k hk]
  have hU0 : fixed π.rep M ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨v0, LocEx.mem_fix.2 fun k hk => by
    obtain ⟨k', hk', rfl⟩ := (Subgroup.mem_inf.1 hk).1
    exact hk', hv0⟩
  have hfin : ∀ K' : Subgroup (locU n w), IsOpen (K' : Set (locU n w)) →
      FiniteDimensional ℂ ↥(fixed π.rep M ⊓ fixed ρ K') := fun K' hK' => by
    let r' : finU (E := E) (n := n) →* locU n w := r.comp (finU (E := E) (n := n)).subtype
    let H : Subgroup (finU (E := E) (n := n)) := L ⊓ (K' ⊓ L.comap (Subgroup.inclusion hle)).comap r'
    have hHo : IsOpen (H : Set (finU (E := E) (n := n))) := hLo.inter ((hK'.inter hLl).preimage (hr.comp continuous_subtype_val))
    haveI := hadm H hHo
    refine Submodule.finiteDimensional_of_le (S₂ := fixed ρf H) fun v hv => LocEx.mem_fix.2 fun k hk => ?_
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    obtain ⟨hkL, hkK, hkL'⟩ := And.intro (Subgroup.mem_inf.1 hk).1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).2)
    have hcM : (r k : UA E n)⁻¹ * k ∈ M := by
      refine Subgroup.mem_inf.2 ⟨⟨(Subgroup.inclusion hle (r' k))⁻¹ * k, L.mul_mem (L.inv_mem hkL') hkL, rfl⟩, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrx (r k), inv_mul_cancel]
    have e1 := LocEx.mem_fix.1 hv1 _ hcM
    have e2 : π.rep (r k : UA E n) v = v := LocEx.mem_fix.1 hv2 _ hkK
    change π.rep (k : UA E n) v = v
    rw [← mul_inv_cancel_left (r k : UA E n) (k : UA E n), map_mul, Module.End.mul_apply, e1, e2]
  obtain ⟨σ, ⟨f, hf0, hf⟩, hσ⟩ := LocEx.exists_irred hρ hKo h2 (fixed π.rep M) hU hU0 hfin
  refine ⟨σ, hσ, σ.irred, π.V.subtype ∘ₗ f, fun e => hf0 (LinearMap.ext fun v => Subtype.ext ?_), fun v => (f v).2,
    fun x v => ?_⟩
  · exact LinearMap.congr_fun e v
  · change (f (σ.ρ x v)).1 = _
    rw [hf]
    rfl

end GlobalTheory.DefU.LocAdm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteMeasureReductionDomainInfinityStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_measure_reduction_domain_infinity : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Λ : Submodule (𝓞 E) (Fin a → E)), Submodule.IsFullLattice E Λ → ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))] (ν : Measure (GL (Fin a) (Cinf E))) [ν.IsHaarMeasure], ∃ Ω : Set (GL (Fin a) (Cinf E)), ν Ω < ⊤ ∧ ∀ y, ∃ γ : GL (Fin a) E, (∀ x, (γ : Matrix (Fin a) (Fin a) E) *ᵥ x ∈ Λ ↔ x ∈ Λ) ∧ ∃ n : ℤ, GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ n) * y ∈ Ω := by
  first | exact @GlobalTheory.GLInfReduction.exists_cover_of_finite_measure | exact GlobalTheory.GLInfReduction.exists_cover_of_finite_measure | (intros; apply GlobalTheory.GLInfReduction.exists_cover_of_finite_measure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsRe
section
noncomputable section

namespace GlobalTheory.Mem.SRe.ColRe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.SRe NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)


set_option maxHeartbeats 4000000 in
def formsRe {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (T : FormsTiedSym D u Ch chOf) :
    FormsTiedSym (reD D Z) u Ch chOf :=
  { T with
    atT := { T.atT with }
    cls := fun i hi h => { T.cls i hi h with }
    val := fun i hi h => { T.val i hi h with }
    lv := fun i hi => { T.lv i hi with }
    ch := fun i h1 h2 β => { T.ch i h1 h2 β with }
    valC := fun i h1 h2 => { T.valC i h1 h2 with }
    dilC := fun i h1 h2 => { T.dilC i h1 h2 with }
    lvC := fun i h1 h2 => { T.lvC i h1 h2 with }
    clsP := { T.clsP with }
    valP := { T.valP with }
    til := { T.til with }
    tilAd := { T.tilAd with } }

end GlobalTheory.Mem.SRe.ColRe

end
end

