// ============================================================
//
//	OFIDO — FIDO2 / WebAuthn Inspector & Verifier
//	Author  : khaled.s.haddad
//	Website : owlsec.org
//	Language: Go (stdlib only) — OWL suite
//
//	Verifies WebAuthn ceremonies offline the way a relying party must:
//	clientDataJSON (type, origin, challenge, crossOrigin), rpIdHash,
//	authenticator flags (UP/UV/BE/BS), signCount clone detection,
//	credential COSE keys, and the cryptographic signatures — attestation
//	statements (packed, fido-u2f, apple, android-key, tpm, none) with
//	x5c chain checks against --roots or the FIDO MDS3 blob, and
//	assertion signatures against the stored credential key.
//	Accepts raw CBOR / hex / base64 or a browser's PublicKeyCredential
//	JSON. Nothing is sent anywhere.
//
// ============================================================
package main

import (
	"bufio"
	"bytes"
	"crypto"
	"crypto/ecdsa"
	"crypto/ed25519"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/rsa"
	_ "crypto/sha1"
	"crypto/sha256"
	_ "crypto/sha512"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/asn1"
	"encoding/base64"
	"encoding/binary"
	"encoding/csv"
	"encoding/hex"
	"encoding/json"
	"encoding/pem"
	"errors"
	"flag"
	"fmt"
	"math"
	"math/big"
	mrand "math/rand"
	"net"
	"net/url"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"time"
	"unicode/utf8"
)

// ---- OWL UI KIT (cyan "owl" house style) — stdlib only. Shared across the suite ----
// CYAN is the primary brand/frame colour; red is reserved for errors and
// CRITICAL/HIGH severities.
const (
	R   = "\033[91m"       // red     — errors / critical
	GRN = "\033[92m"       // green   — success / low
	YLW = "\033[93m"       // yellow  — prompts / warning text
	CY  = "\033[96m"       // cyan    — primary brand & frames
	W   = "\033[97m"       // white   — body text
	B   = "\033[1m"        // bold
	X   = "\033[0m"        // reset
	MG  = "\033[95m"       // magenta — suite name / accents
	DIM = "\033[2m"        // dim     — secondary text
	OR  = "\033[38;5;208m" // orange  — warning markers
	GY  = "\033[90m"       // gray    — muted
)

var noColor = os.Getenv("NO_COLOR") != "" || !isatty()

func isatty() bool { fi, _ := os.Stdout.Stat(); return (fi.Mode() & os.ModeCharDevice) != 0 }
func col(s string, c ...string) string {
	if noColor {
		return s
	}
	return strings.Join(c, "") + s + X
}
func clear()           { fmt.Print("\033[H\033[2J") }
func rule()            { fmt.Println(col(strings.Repeat("─", 66), CY)) }
func okMsg(s string)   { fmt.Println("  " + col("[✔] ", GRN+B) + col(s, W)) }
func errMsg(s string)  { fmt.Println("  " + col("[✘] ", R+B) + col(s, R)) }
func warnMsg(s string) { fmt.Println("  " + col("[!] ", OR+B) + col(s, YLW)) }
func info(s string)    { fmt.Println("  " + col("[*] ", CY) + col(s, DIM+W)) }
func kv(k, v string)   { fmt.Println("  " + col("│  ", CY) + col(pad(k+":", 20), DIM) + col(v, W)) }

const BANNER = `
 ██████╗ ███████╗██╗██████╗  ██████╗
██╔═══██╗██╔════╝██║██╔══██╗██╔═══██╗
██║   ██║█████╗  ██║██║  ██║██║   ██║
██║   ██║██╔══╝  ██║██║  ██║██║   ██║
╚██████╔╝██║     ██║██████╔╝╚██████╔╝
 ╚═════╝ ╚═╝     ╚═╝╚═════╝  ╚═════╝
`

const APPNAME = "OFIDO"
const SUITE = "Owl Identity Suite"
const TAGLINE = "FIDO2 / WebAuthn Inspector & Verifier"
const SUBLINE = "Signatures · Attestation · MDS · RP Options · Credential Store · getInfo · Test Gen"
const VERSION = "1.1"
const AUTHOR = "khaled.s.haddad"
const WEBSITE = "owlsec.org"

// banner prints the cyan ANSI-Shadow wordmark and the suite identity block.
func banner() {
	fmt.Println(col(BANNER, CY))
	fmt.Println("  " + col(SUITE+"  ", B+MG) + col("v"+VERSION, YLW))
	fmt.Println("  " + col(SUBLINE, W))
	fmt.Println()
	fmt.Println("  " + col("Developer : ", DIM) + col(AUTHOR, CY) +
		col("   |   Website : ", DIM) + col(WEBSITE, CY))
	rule()
	fmt.Println()
}

var stdin = bufio.NewReader(os.Stdin)

func prompt(label string) string {
	fmt.Print("  " + col("[»] ", YLW) + col(label+": ", W))
	s, _ := stdin.ReadString('\n')
	return strings.TrimSpace(s)
}
func pause() {
	fmt.Print(col("\n  [↩] Press Enter to continue...", YLW))
	stdin.ReadString('\n')
}

// sectionHeader prints a ⬡ heading between two cyan rules.
func sectionHeader(s string) {
	rule()
	fmt.Println("  " + col("⬡  "+s, B+CY))
	rule()
	fmt.Println()
}

func stripANSI(s string) string {
	var b strings.Builder
	esc := false
	for _, r := range s {
		if r == '\033' {
			esc = true
			continue
		}
		if esc {
			if r == 'm' {
				esc = false
			}
			continue
		}
		b.WriteRune(r)
	}
	return b.String()
}

func vlen(s string) int { return utf8.RuneCountInString(stripANSI(s)) }
func pad(s string, n int) string {
	if l := vlen(s); l < n {
		return s + strings.Repeat(" ", n-l)
	}
	return s
}

func trunc(s string, n int) string {
	r := []rune(s)
	if len(r) <= n {
		return s
	}
	return string(r[:n-1]) + "…"
}

// table prints aligned columns with a cyan frame.
func table(headers []string, rows [][]string) {
	w := make([]int, len(headers))
	for i, h := range headers {
		w[i] = vlen(h)
	}
	for _, r := range rows {
		for i, c := range r {
			if i < len(w) && vlen(c) > w[i] {
				w[i] = vlen(c)
			}
		}
	}
	var hb strings.Builder
	for i, h := range headers {
		hb.WriteString(col(pad(h, w[i]), CY+B))
		if i < len(headers)-1 {
			hb.WriteString(col(" │ ", CY))
		}
	}
	fmt.Println("  " + hb.String())
	seg := make([]string, len(w))
	for i := range w {
		seg[i] = strings.Repeat("─", w[i])
	}
	fmt.Println("  " + col(strings.Join(seg, "─┼─"), CY))
	for _, r := range rows {
		var rb strings.Builder
		for i := range headers {
			v := ""
			if i < len(r) {
				v = r[i]
			}
			rb.WriteString(pad(col(v, W), w[i]))
			if i < len(headers)-1 {
				rb.WriteString(col(" │ ", CY))
			}
		}
		fmt.Println("  " + rb.String())
	}
}

const (
	SevCritical = "CRITICAL"
	SevHigh     = "HIGH"
	SevMedium   = "MEDIUM"
	SevLow      = "LOW"
	SevInfo     = "INFO"
)

var sevRank = map[string]int{SevCritical: 5, SevHigh: 4, SevMedium: 3, SevLow: 2, SevInfo: 1}

func sevColor(s string) string {
	switch s {
	case SevCritical:
		return col(s, R+B)
	case SevHigh:
		return col(s, R)
	case SevMedium:
		return col(s, OR)
	case SevLow:
		return col(s, YLW)
	}
	return col(s, DIM)
}

func gradeColor(g string) string {
	switch g {
	case "A+", "A":
		return col(g, GRN+B)
	case "B":
		return col(g, CY+B)
	case "C":
		return col(g, YLW+B)
	case "D":
		return col(g, OR+B)
	}
	return col(g, R+B)
}

// ====================================================================
//  CBOR (RFC 8949) — definite-length subset used by WebAuthn, hardened:
//  nesting depth, item counts and lengths are bounded by the input size.
// ====================================================================

type cborType int

const (
	cborUint cborType = iota
	cborNint
	cborBytes
	cborText
	cborArray
	cborMap
	cborTag
	cborSimple
	cborFloat
)

type cborValue struct {
	Type   cborType
	Uint   uint64
	Neg    int64
	Bytes  []byte
	Text   string
	Items  []cborValue
	Pairs  []cborPair
	Tag    uint64
	Tagged *cborValue
	Simple byte
	Float  float64
}

type cborPair struct{ K, V cborValue }

type cborReader struct {
	b     []byte
	i     int
	depth int
	items int
}

const cborMaxDepth = 32

func newCBOR(b []byte) *cborReader { return &cborReader{b: b} }

func (r *cborReader) readByte() (byte, error) {
	if r.i >= len(r.b) {
		return 0, errors.New("CBOR: unexpected end of data")
	}
	c := r.b[r.i]
	r.i++
	return c, nil
}

func (r *cborReader) readN(n uint64) ([]byte, error) {
	if n > uint64(len(r.b)-r.i) {
		return nil, fmt.Errorf("CBOR: length %d exceeds the remaining %d bytes", n, len(r.b)-r.i)
	}
	out := r.b[r.i : r.i+int(n)]
	r.i += int(n)
	return out, nil
}

func (r *cborReader) additional(ai byte) (uint64, error) {
	switch {
	case ai < 24:
		return uint64(ai), nil
	case ai == 24:
		b, err := r.readByte()
		return uint64(b), err
	case ai == 25:
		b, err := r.readN(2)
		if err != nil {
			return 0, err
		}
		return uint64(binary.BigEndian.Uint16(b)), nil
	case ai == 26:
		b, err := r.readN(4)
		if err != nil {
			return 0, err
		}
		return uint64(binary.BigEndian.Uint32(b)), nil
	case ai == 27:
		b, err := r.readN(8)
		if err != nil {
			return 0, err
		}
		return binary.BigEndian.Uint64(b), nil
	case ai == 31:
		return 0, errors.New("CBOR: indefinite-length items are not allowed in WebAuthn (CTAP2 canonical CBOR)")
	}
	return 0, fmt.Errorf("CBOR: reserved additional info %d", ai)
}

func (r *cborReader) decode() (cborValue, error) {
	r.depth++
	defer func() { r.depth-- }()
	if r.depth > cborMaxDepth {
		return cborValue{}, errors.New("CBOR: nesting deeper than 32 levels")
	}
	if r.items++; r.items > 100000 {
		return cborValue{}, errors.New("CBOR: more than 100000 items")
	}
	b, err := r.readByte()
	if err != nil {
		return cborValue{}, err
	}
	major, ai := b>>5, b&0x1f
	if major == 7 {
		switch ai {
		case 20, 21, 22, 23:
			return cborValue{Type: cborSimple, Simple: ai}, nil
		case 24:
			s, err := r.readByte()
			return cborValue{Type: cborSimple, Simple: s}, err
		case 25:
			bs, err := r.readN(2)
			if err != nil {
				return cborValue{}, err
			}
			return cborValue{Type: cborFloat, Float: halfFloat(binary.BigEndian.Uint16(bs))}, nil
		case 26:
			bs, err := r.readN(4)
			if err != nil {
				return cborValue{}, err
			}
			return cborValue{Type: cborFloat, Float: float64(math.Float32frombits(binary.BigEndian.Uint32(bs)))}, nil
		case 27:
			bs, err := r.readN(8)
			if err != nil {
				return cborValue{}, err
			}
			return cborValue{Type: cborFloat, Float: math.Float64frombits(binary.BigEndian.Uint64(bs))}, nil
		case 31:
			return cborValue{}, errors.New("CBOR: unexpected break")
		}
		return cborValue{Type: cborSimple, Simple: ai}, nil
	}
	n, err := r.additional(ai)
	if err != nil {
		return cborValue{}, err
	}
	// every element takes ≥ 1 byte: a count above the remaining input is a lie
	remaining := uint64(len(r.b) - r.i)
	switch major {
	case 0:
		return cborValue{Type: cborUint, Uint: n}, nil
	case 1:
		if n > math.MaxInt64 {
			return cborValue{}, errors.New("CBOR: negative integer out of range")
		}
		return cborValue{Type: cborNint, Neg: -1 - int64(n)}, nil
	case 2:
		bs, err := r.readN(n)
		return cborValue{Type: cborBytes, Bytes: bs}, err
	case 3:
		bs, err := r.readN(n)
		if err == nil && !utf8.Valid(bs) {
			err = errors.New("CBOR: text string is not valid UTF-8")
		}
		return cborValue{Type: cborText, Text: string(bs)}, err
	case 4:
		if n > remaining {
			return cborValue{}, fmt.Errorf("CBOR: array of %d items in %d bytes", n, remaining)
		}
		items := make([]cborValue, 0, n)
		for i := uint64(0); i < n; i++ {
			v, err := r.decode()
			if err != nil {
				return cborValue{}, err
			}
			items = append(items, v)
		}
		return cborValue{Type: cborArray, Items: items}, nil
	case 5:
		if n > remaining/2 {
			return cborValue{}, fmt.Errorf("CBOR: map of %d pairs in %d bytes", n, remaining)
		}
		pairs := make([]cborPair, 0, n)
		for i := uint64(0); i < n; i++ {
			k, err := r.decode()
			if err != nil {
				return cborValue{}, err
			}
			v, err := r.decode()
			if err != nil {
				return cborValue{}, err
			}
			pairs = append(pairs, cborPair{K: k, V: v})
		}
		return cborValue{Type: cborMap, Pairs: pairs}, nil
	case 6:
		inner, err := r.decode()
		if err != nil {
			return cborValue{}, err
		}
		return cborValue{Type: cborTag, Tag: n, Tagged: &inner}, nil
	}
	return cborValue{}, fmt.Errorf("CBOR: major type %d", major)
}

func halfFloat(h uint16) float64 {
	exp, mant := int(h>>10)&0x1f, float64(h&0x3ff)
	v := 0.0
	switch exp {
	case 0:
		v = mant * math.Pow(2, -24)
	case 31:
		v = math.Inf(1)
		if mant != 0 {
			v = math.NaN()
		}
	default:
		v = (1 + mant/1024) * math.Pow(2, float64(exp-15))
	}
	if h&0x8000 != 0 {
		v = -v
	}
	return v
}

// decodeCBOR decodes one item and rejects trailing bytes.
func decodeCBOR(b []byte) (cborValue, error) {
	r := newCBOR(b)
	v, err := r.decode()
	if err == nil && r.i != len(b) {
		err = fmt.Errorf("CBOR: %d trailing byte(s)", len(b)-r.i)
	}
	return v, err
}

func (v cborValue) asInt() (int64, bool) {
	switch v.Type {
	case cborUint:
		if v.Uint > math.MaxInt64 {
			return 0, false
		}
		return int64(v.Uint), true
	case cborNint:
		return v.Neg, true
	}
	return 0, false
}

func (v cborValue) asBytes() ([]byte, bool) {
	if v.Type == cborBytes {
		return v.Bytes, true
	}
	return nil, false
}

func (v cborValue) asText() (string, bool) {
	if v.Type == cborText {
		return v.Text, true
	}
	return "", false
}

func (v cborValue) mapGetString(key string) (cborValue, bool) {
	if v.Type != cborMap {
		return cborValue{}, false
	}
	for _, p := range v.Pairs {
		if p.K.Type == cborText && p.K.Text == key {
			return p.V, true
		}
	}
	return cborValue{}, false
}

func (v cborValue) mapGetInt(key int64) (cborValue, bool) {
	if v.Type != cborMap {
		return cborValue{}, false
	}
	for _, p := range v.Pairs {
		if n, ok := p.K.asInt(); ok && n == key {
			return p.V, true
		}
	}
	return cborValue{}, false
}

// pretty renders CBOR diagnostic notation (RFC 8949 §8).
func (v cborValue) pretty(indent int) string {
	pad := strings.Repeat("  ", indent)
	switch v.Type {
	case cborUint:
		return strconv.FormatUint(v.Uint, 10)
	case cborNint:
		return strconv.FormatInt(v.Neg, 10)
	case cborBytes:
		if len(v.Bytes) > 64 {
			return "h'" + hex.EncodeToString(v.Bytes[:32]) + "…' (" + strconv.Itoa(len(v.Bytes)) + " bytes)"
		}
		return "h'" + hex.EncodeToString(v.Bytes) + "'"
	case cborText:
		return strconv.Quote(v.Text)
	case cborSimple:
		switch v.Simple {
		case 20:
			return "false"
		case 21:
			return "true"
		case 22:
			return "null"
		case 23:
			return "undefined"
		}
		return fmt.Sprintf("simple(%d)", v.Simple)
	case cborFloat:
		return strconv.FormatFloat(v.Float, 'g', -1, 64)
	case cborTag:
		return fmt.Sprintf("%d(%s)", v.Tag, v.Tagged.pretty(indent))
	case cborArray:
		if len(v.Items) == 0 {
			return "[]"
		}
		var b strings.Builder
		b.WriteString("[\n")
		for i, it := range v.Items {
			b.WriteString(pad + "  " + it.pretty(indent+1))
			if i+1 < len(v.Items) {
				b.WriteString(",")
			}
			b.WriteByte('\n')
		}
		return b.String() + pad + "]"
	case cborMap:
		if len(v.Pairs) == 0 {
			return "{}"
		}
		var b strings.Builder
		b.WriteString("{\n")
		for i, p := range v.Pairs {
			b.WriteString(pad + "  " + p.K.pretty(indent+1) + ": " + p.V.pretty(indent+1))
			if i+1 < len(v.Pairs) {
				b.WriteString(",")
			}
			b.WriteByte('\n')
		}
		return b.String() + pad + "}"
	}
	return "?"
}

type cborWriter struct{ b bytes.Buffer }

func (w *cborWriter) putInitial(major byte, n uint64) {
	switch {
	case n < 24:
		w.b.WriteByte(major<<5 | byte(n))
	case n < 256:
		w.b.Write([]byte{major<<5 | 24, byte(n)})
	case n < 65536:
		w.b.WriteByte(major<<5 | 25)
		w.b.Write(binary.BigEndian.AppendUint16(nil, uint16(n)))
	case n < 1<<32:
		w.b.WriteByte(major<<5 | 26)
		w.b.Write(binary.BigEndian.AppendUint32(nil, uint32(n)))
	default:
		w.b.WriteByte(major<<5 | 27)
		w.b.Write(binary.BigEndian.AppendUint64(nil, n))
	}
}

func (w *cborWriter) encode(v cborValue) {
	switch v.Type {
	case cborUint:
		w.putInitial(0, v.Uint)
	case cborNint:
		w.putInitial(1, uint64(-1-v.Neg))
	case cborBytes:
		w.putInitial(2, uint64(len(v.Bytes)))
		w.b.Write(v.Bytes)
	case cborText:
		w.putInitial(3, uint64(len(v.Text)))
		w.b.WriteString(v.Text)
	case cborArray:
		w.putInitial(4, uint64(len(v.Items)))
		for _, it := range v.Items {
			w.encode(it)
		}
	case cborMap:
		w.putInitial(5, uint64(len(v.Pairs)))
		for _, p := range v.Pairs {
			w.encode(p.K)
			w.encode(p.V)
		}
	case cborTag:
		w.putInitial(6, v.Tag)
		w.encode(*v.Tagged)
	case cborSimple:
		if v.Simple < 24 {
			w.b.WriteByte(0xe0 | v.Simple)
		} else {
			w.b.Write([]byte{0xf8, v.Simple})
		}
	case cborFloat:
		w.b.WriteByte(0xfb)
		w.b.Write(binary.BigEndian.AppendUint64(nil, math.Float64bits(v.Float)))
	}
}

func encodeCBOR(v cborValue) []byte { var w cborWriter; w.encode(v); return w.b.Bytes() }

// small constructors for building test vectors
func cInt(n int64) cborValue {
	if n < 0 {
		return cborValue{Type: cborNint, Neg: n}
	}
	return cborValue{Type: cborUint, Uint: uint64(n)}
}
func cBytes(b []byte) cborValue { return cborValue{Type: cborBytes, Bytes: b} }
func cText(s string) cborValue  { return cborValue{Type: cborText, Text: s} }
func cMap(kv ...cborValue) cborValue {
	v := cborValue{Type: cborMap}
	for i := 0; i+1 < len(kv); i += 2 {
		v.Pairs = append(v.Pairs, cborPair{kv[i], kv[i+1]})
	}
	return v
}

// ====================================================================
//  AUTHENTICATOR DATA
// ====================================================================

type AuthDataFlags struct {
	UP, UV, BE, BS, AT, ED bool
	Raw                    byte
}

func parseFlags(b byte) AuthDataFlags {
	return AuthDataFlags{UP: b&0x01 != 0, UV: b&0x04 != 0, BE: b&0x08 != 0, BS: b&0x10 != 0, AT: b&0x40 != 0, ED: b&0x80 != 0, Raw: b}
}

func (f AuthDataFlags) String() string {
	var p []string
	for _, x := range []struct {
		on bool
		n  string
	}{{f.UP, "UP"}, {f.UV, "UV"}, {f.BE, "BE"}, {f.BS, "BS"}, {f.AT, "AT"}, {f.ED, "ED"}} {
		if x.on {
			p = append(p, x.n)
		}
	}
	if len(p) == 0 {
		return fmt.Sprintf("0x%02x (none)", f.Raw)
	}
	return fmt.Sprintf("0x%02x %s", f.Raw, strings.Join(p, "|"))
}

type AttestedCredData struct {
	AAGUID  []byte
	CredID  []byte
	COSEKey []byte
	Key     *COSEKey
}

type AuthData struct {
	RPIDHash   []byte
	Flags      AuthDataFlags
	SignCount  uint32
	Attested   *AttestedCredData
	Extensions []byte
	Raw        []byte
}

func parseAuthData(b []byte) (*AuthData, error) {
	if len(b) < 37 {
		return nil, fmt.Errorf("authenticatorData too short (%d bytes, need ≥ 37)", len(b))
	}
	ad := &AuthData{Raw: b, RPIDHash: b[0:32], Flags: parseFlags(b[32]), SignCount: binary.BigEndian.Uint32(b[33:37])}
	off := 37
	if ad.Flags.AT {
		if len(b) < off+18 {
			return nil, errors.New("attested credential data truncated")
		}
		acd := &AttestedCredData{AAGUID: b[off : off+16]}
		off += 16
		idLen := int(binary.BigEndian.Uint16(b[off:]))
		off += 2
		if idLen > 1023 {
			return nil, fmt.Errorf("credentialId length %d exceeds the WebAuthn maximum of 1023", idLen)
		}
		if len(b) < off+idLen {
			return nil, errors.New("credential id truncated")
		}
		acd.CredID = b[off : off+idLen]
		off += idLen
		r := newCBOR(b[off:])
		if _, err := r.decode(); err != nil {
			return nil, fmt.Errorf("credential public key: %v", err)
		}
		acd.COSEKey = b[off : off+r.i]
		off += r.i
		ck, err := parseCOSEKey(acd.COSEKey)
		if err != nil {
			return nil, fmt.Errorf("credential public key: %v", err)
		}
		acd.Key = ck
		ad.Attested = acd
	}
	if ad.Flags.ED {
		ad.Extensions = b[off:]
	} else if off < len(b) {
		return nil, fmt.Errorf("%d trailing byte(s) after authenticatorData (ED flag not set)", len(b)-off)
	}
	return ad, nil
}

// ====================================================================
//  COSE KEYS → crypto public keys
// ====================================================================

type COSEKey struct {
	Kty, Alg, Crv int64
	X, Y, N, E    []byte
	Pub           crypto.PublicKey
	Err           string // why Pub could not be built
}

type COSEAlg struct {
	Name, Description, KeyType, Status string
	Hash                               crypto.Hash
}

var coseAlgDB = map[int64]COSEAlg{
	-7:     {"ES256", "ECDSA w/ SHA-256", "EC2", "recommended", crypto.SHA256},
	-8:     {"EdDSA", "Ed25519", "OKP", "recommended", 0},
	-35:    {"ES384", "ECDSA w/ SHA-384", "EC2", "optional", crypto.SHA384},
	-36:    {"ES512", "ECDSA w/ SHA-512", "EC2", "optional", crypto.SHA512},
	-257:   {"RS256", "RSASSA-PKCS1-v1_5 SHA-256", "RSA", "optional", crypto.SHA256},
	-258:   {"RS384", "RSASSA-PKCS1-v1_5 SHA-384", "RSA", "optional", crypto.SHA384},
	-259:   {"RS512", "RSASSA-PKCS1-v1_5 SHA-512", "RSA", "optional", crypto.SHA512},
	-37:    {"PS256", "RSASSA-PSS SHA-256", "RSA", "optional", crypto.SHA256},
	-38:    {"PS384", "RSASSA-PSS SHA-384", "RSA", "optional", crypto.SHA384},
	-39:    {"PS512", "RSASSA-PSS SHA-512", "RSA", "optional", crypto.SHA512},
	-47:    {"ES256K", "ECDSA secp256k1 SHA-256", "EC2", "not-for-webauthn", crypto.SHA256},
	-65535: {"RS1", "RSASSA-PKCS1-v1_5 SHA-1", "RSA", "legacy-u2f", crypto.SHA1},
}

var coseKtyNames = map[int64]string{1: "OKP", 2: "EC2", 3: "RSA", 4: "Symmetric"}
var coseCrvNames = map[int64]string{1: "P-256", 2: "P-384", 3: "P-521", 4: "X25519", 5: "X448", 6: "Ed25519", 7: "Ed448", 8: "secp256k1"}

func algName(a int64) string {
	if x, ok := coseAlgDB[a]; ok {
		return x.Name
	}
	return fmt.Sprintf("alg(%d)", a)
}

func parseCOSEKey(b []byte) (*COSEKey, error) {
	v, err := decodeCBOR(b)
	if err != nil {
		return nil, err
	}
	if v.Type != cborMap {
		return nil, errors.New("COSE key must be a CBOR map")
	}
	ck := &COSEKey{}
	gi := func(k int64) (int64, bool) {
		if x, ok := v.mapGetInt(k); ok {
			return x.asInt()
		}
		return 0, false
	}
	gb := func(k int64) []byte {
		if x, ok := v.mapGetInt(k); ok {
			if bs, ok := x.asBytes(); ok {
				return bs
			}
		}
		return nil
	}
	var ok bool
	if ck.Kty, ok = gi(1); !ok {
		return nil, errors.New("COSE key has no kty (1)")
	}
	ck.Alg, _ = gi(3)
	switch ck.Kty {
	case 2: // EC2
		ck.Crv, _ = gi(-1)
		ck.X, ck.Y = gb(-2), gb(-3)
		var curve elliptic.Curve
		switch ck.Crv {
		case 1:
			curve = elliptic.P256()
		case 2:
			curve = elliptic.P384()
		case 3:
			curve = elliptic.P521()
		}
		size := 0
		if curve != nil {
			size = (curve.Params().BitSize + 7) / 8
		}
		switch {
		case curve == nil:
			ck.Err = "curve " + coseCrvNames[ck.Crv] + " is not supported by the Go standard library"
		case len(ck.X) != size || len(ck.Y) != size:
			ck.Err = fmt.Sprintf("EC coordinates must be %d bytes (x=%d, y=%d)", size, len(ck.X), len(ck.Y))
		default:
			x, y := new(big.Int).SetBytes(ck.X), new(big.Int).SetBytes(ck.Y)
			if !curve.IsOnCurve(x, y) {
				ck.Err = "EC point is not on the curve (invalid-curve attack / corrupted key)"
			} else {
				ck.Pub = &ecdsa.PublicKey{Curve: curve, X: x, Y: y}
			}
		}
	case 1: // OKP
		ck.Crv, _ = gi(-1)
		ck.X = gb(-2)
		switch {
		case ck.Crv != 6:
			ck.Err = "OKP curve " + coseCrvNames[ck.Crv] + " is not supported"
		case len(ck.X) != ed25519.PublicKeySize:
			ck.Err = fmt.Sprintf("Ed25519 key must be 32 bytes, got %d", len(ck.X))
		default:
			ck.Pub = ed25519.PublicKey(ck.X)
		}
	case 3: // RSA
		ck.N, ck.E = gb(-1), gb(-2)
		e := new(big.Int).SetBytes(ck.E)
		if len(ck.N) == 0 || !e.IsInt64() || e.Int64() < 3 || e.Int64() > 1<<31 {
			ck.Err = "RSA key needs n and a sane exponent"
		} else {
			ck.Pub = &rsa.PublicKey{N: new(big.Int).SetBytes(ck.N), E: int(e.Int64())}
		}
	default:
		ck.Err = fmt.Sprintf("unsupported kty %d", ck.Kty)
	}
	return ck, nil
}

func (ck *COSEKey) summarize() []KV {
	out := []KV{{"kty", coseKtyNames[ck.Kty]}, {"alg", fmt.Sprintf("%s (%d)", algName(ck.Alg), ck.Alg)}}
	switch ck.Kty {
	case 1, 2:
		out = append(out, KV{"crv", coseCrvNames[ck.Crv]})
		if len(ck.X) > 0 {
			out = append(out, KV{"x", hex.EncodeToString(ck.X)})
		}
		if len(ck.Y) > 0 {
			out = append(out, KV{"y", hex.EncodeToString(ck.Y)})
		}
	case 3:
		out = append(out, KV{"n_bits", strconv.Itoa(new(big.Int).SetBytes(ck.N).BitLen())}, KV{"e", new(big.Int).SetBytes(ck.E).String()})
	}
	if ck.Err != "" {
		out = append(out, KV{"usable", "no — " + ck.Err})
	} else if spki, err := x509.MarshalPKIXPublicKey(ck.Pub); err == nil {
		h := sha256.Sum256(spki)
		out = append(out, KV{"spki_sha256", hex.EncodeToString(h[:])})
	}
	return out
}

// pubKeyFromCrypto wraps a certificate / PEM key so verify() can use it.
func coseFromCrypto(pub crypto.PublicKey, alg int64) *COSEKey {
	ck := &COSEKey{Pub: pub, Alg: alg}
	switch k := pub.(type) {
	case *ecdsa.PublicKey:
		ck.Kty = 2
		switch k.Curve {
		case elliptic.P256():
			ck.Crv = 1
		case elliptic.P384():
			ck.Crv = 2
		case elliptic.P521():
			ck.Crv = 3
		}
	case ed25519.PublicKey:
		ck.Kty, ck.Crv = 1, 6
	case *rsa.PublicKey:
		ck.Kty = 3
		ck.N = k.N.Bytes()
		ck.E = big.NewInt(int64(k.E)).Bytes()
	}
	return ck
}

// sameKey compares two public keys (credential key vs certificate key).
func sameKey(a, b crypto.PublicKey) bool {
	type eq interface{ Equal(crypto.PublicKey) bool }
	if x, ok := a.(eq); ok {
		return x.Equal(b)
	}
	return false
}

// verifySig checks sig over msg with pub using COSE algorithm alg.
func verifySig(pub crypto.PublicKey, alg int64, msg, sig []byte) error {
	a, ok := coseAlgDB[alg]
	if !ok {
		return fmt.Errorf("unknown COSE algorithm %d", alg)
	}
	if alg == -47 {
		return errors.New("secp256k1 (ES256K) is not supported by the Go standard library")
	}
	digest := func() []byte {
		h := a.Hash.New()
		h.Write(msg)
		return h.Sum(nil)
	}
	switch k := pub.(type) {
	case *ecdsa.PublicKey:
		if a.KeyType != "EC2" {
			return fmt.Errorf("algorithm %s does not match an EC key", a.Name)
		}
		if !ecdsa.VerifyASN1(k, digest(), sig) {
			return errors.New("ECDSA signature does not verify")
		}
	case ed25519.PublicKey:
		if alg != -8 {
			return fmt.Errorf("algorithm %s does not match an Ed25519 key", a.Name)
		}
		if !ed25519.Verify(k, msg, sig) {
			return errors.New("Ed25519 signature does not verify")
		}
	case *rsa.PublicKey:
		if a.KeyType != "RSA" {
			return fmt.Errorf("algorithm %s does not match an RSA key", a.Name)
		}
		var err error
		if strings.HasPrefix(a.Name, "PS") {
			err = rsa.VerifyPSS(k, a.Hash, digest(), sig, &rsa.PSSOptions{SaltLength: rsa.PSSSaltLengthAuto})
		} else {
			err = rsa.VerifyPKCS1v15(k, a.Hash, digest(), sig)
		}
		if err != nil {
			return fmt.Errorf("RSA signature does not verify: %v", err)
		}
	default:
		return errors.New("no usable public key")
	}
	return nil
}

// certAlg maps a certificate key to the COSE alg a statement should use.
func certAlg(c *x509.Certificate, stated int64) int64 {
	if stated != 0 {
		return stated
	}
	switch c.PublicKeyAlgorithm {
	case x509.ECDSA:
		return -7
	case x509.Ed25519:
		return -8
	}
	return -257
}

// ====================================================================
//  AAGUIDS + FIDO METADATA SERVICE (offline)
// ====================================================================

type AAGUIDInfo struct {
	Name   string
	Kind   string // hardware key | platform | password manager
	Source string // built-in | MDS
	Status string // latest MDS status report
	Roots  []*x509.Certificate
}

// builtinAAGUIDs: a small, well-known subset (community passkey AAGUID list
// and vendor documentation). Load the FIDO MDS3 blob with --mds for the
// authoritative list, root certificates and status reports.
var builtinAAGUIDs = map[string]AAGUIDInfo{
	"ea9b8d664d011d213ce4b6b48cb575d4": {Name: "Google Password Manager", Kind: "password manager"},
	"adce000235bcc60a648b0b25f1f05503": {Name: "Chrome on Mac", Kind: "platform"},
	"fbfc3007154e4ecc8c0b6e020557d7bd": {Name: "Apple iCloud Keychain / Passwords", Kind: "password manager"},
	"dd4ec289e01d41c9bb8970fa845d4bf2": {Name: "iCloud Keychain (Managed)", Kind: "password manager"},
	"08987058cadc4b81b6e130de50dcbe96": {Name: "Windows Hello", Kind: "platform"},
	"9ddd1817af5a4672a2b93e3dd95000a9": {Name: "Windows Hello", Kind: "platform"},
	"6028b017b1d44c02b4b3afcdafc96bb2": {Name: "Windows Hello", Kind: "platform"},
	"bada5566a7aa401fbd9645619a55120d": {Name: "1Password", Kind: "password manager"},
	"d548826e79b4db40a3d811116f7e8349": {Name: "Bitwarden", Kind: "password manager"},
	"531126d6e717415c93203d9aa6981239": {Name: "Dashlane", Kind: "password manager"},
	"fdb141b25d84443e8a354698c205a502": {Name: "KeePassXC", Kind: "password manager"},
	"53414d53554e47000000000000000000": {Name: "Samsung Pass", Kind: "password manager"},
	"50726f746f6e5061737350726f746f6e": {Name: "Proton Pass", Kind: "password manager"},
	"cb69481e8ff7403993ec0a2729a154a8": {Name: "YubiKey 5 Series", Kind: "hardware key"},
	"fa2b99dc9e3942578f924a30d23c4118": {Name: "YubiKey 5 Series with NFC", Kind: "hardware key"},
	"2fc0579f811347eab116bb5a8db9202a": {Name: "YubiKey 5 Series with NFC", Kind: "hardware key"},
	"c5ef55ffad9a4b9fb580adebafe026d0": {Name: "YubiKey 5Ci", Kind: "hardware key"},
	"ee882879721c491397753dfcce97072a": {Name: "YubiKey 5 Series", Kind: "hardware key"},
	"a4e9fc6d4cbe4758b8ba37598bb5bbaa": {Name: "Security Key NFC by Yubico", Kind: "hardware key"},
	"f8a011f38c0a4d15800617111f9edc7d": {Name: "Security Key by Yubico", Kind: "hardware key"},
	"b92c3f9ac0144056887f140a2501163b": {Name: "Security Key by Yubico", Kind: "hardware key"},
	"42b4fb4a286643b29bf76c6669c2e5d3": {Name: "Google Titan Security Key v2", Kind: "hardware key"},
}

var mdsDB = map[string]AAGUIDInfo{}
var mdsLoaded string

func lookupAAGUID(b []byte) (AAGUIDInfo, bool) {
	h := hex.EncodeToString(b)
	if x, ok := mdsDB[h]; ok {
		return x, true
	}
	if x, ok := builtinAAGUIDs[h]; ok {
		x.Source = "built-in"
		return x, true
	}
	return AAGUIDInfo{}, false
}

func canonAAGUID(b []byte) string {
	h := hex.EncodeToString(b)
	if len(h) != 32 {
		return h
	}
	return h[0:8] + "-" + h[8:12] + "-" + h[12:16] + "-" + h[16:20] + "-" + h[20:32]
}

// loadMDS reads the FIDO MDS3 BLOB (the JWT from mds3.fidoalliance.org) or
// its decoded JSON payload. The JWT signature is NOT verified offline.
func loadMDS(path string) (int, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return 0, err
	}
	data = bytes.TrimSpace(data)
	if len(data) > 0 && data[0] != '{' {
		parts := bytes.Split(data, []byte("."))
		if len(parts) != 3 {
			return 0, errors.New("MDS: neither JSON nor a JWT")
		}
		if data, err = base64.RawURLEncoding.DecodeString(string(parts[1])); err != nil {
			return 0, fmt.Errorf("MDS payload: %v", err)
		}
	}
	var doc struct {
		No      int    `json:"no"`
		Next    string `json:"nextUpdate"`
		Entries []struct {
			AAGUID   string `json:"aaguid"`
			Metadata struct {
				Description string   `json:"description"`
				Roots       []string `json:"attestationRootCertificates"`
			} `json:"metadataStatement"`
			Status []struct {
				Status string `json:"status"`
				Date   string `json:"effectiveDate"`
			} `json:"statusReports"`
		} `json:"entries"`
	}
	if err := json.Unmarshal(data, &doc); err != nil {
		return 0, fmt.Errorf("MDS JSON: %v", err)
	}
	n := 0
	for _, e := range doc.Entries {
		if e.AAGUID == "" {
			continue
		}
		info := AAGUIDInfo{Name: e.Metadata.Description, Source: fmt.Sprintf("MDS #%d", doc.No)}
		if len(e.Status) > 0 {
			last := e.Status[0]
			for _, s := range e.Status {
				if s.Date >= last.Date {
					last = s
				}
			}
			info.Status = last.Status
		}
		for _, r := range e.Metadata.Roots {
			if der, err := base64.StdEncoding.DecodeString(r); err == nil {
				if c, err := x509.ParseCertificate(der); err == nil {
					info.Roots = append(info.Roots, c)
				}
			}
		}
		mdsDB[strings.ReplaceAll(strings.ToLower(e.AAGUID), "-", "")] = info
		n++
	}
	mdsLoaded = fmt.Sprintf("%s (BLOB #%d, next update %s, signature not verified offline)", filepath.Base(path), doc.No, doc.Next)
	return n, nil
}

// statuses that mean the authenticator must not be trusted
var badStatus = map[string]bool{"REVOKED": true, "ATTESTATION_KEY_COMPROMISE": true, "USER_VERIFICATION_BYPASS": true,
	"USER_KEY_REMOTE_COMPROMISE": true, "USER_KEY_PHYSICAL_COMPROMISE": true}

// ====================================================================
//  FINDINGS
// ====================================================================

type Finding struct {
	ID       string `json:"id"`
	Severity string `json:"severity"`
	Title    string `json:"title"`
	Evidence string `json:"evidence,omitempty"`
	Fix      string `json:"fix,omitempty"`
	Category string `json:"category"`
}

type KV struct {
	K string `json:"key"`
	V string `json:"value"`
}

type Report struct {
	Tool      string    `json:"tool"`
	Version   string    `json:"version"`
	Target    string    `json:"target"`
	Kind      string    `json:"kind"` // registration | authentication | cose | aaguid
	Generated string    `json:"generated"`
	Verdict   string    `json:"verdict"`
	Stats     []KV      `json:"facts"`
	Findings  []Finding `json:"findings"`
	Grade     string    `json:"grade"`
	Score     int       `json:"score"`
}

func newReport(target, kind string) *Report {
	return &Report{Tool: APPNAME, Version: VERSION, Target: target, Kind: kind,
		Generated: time.Now().UTC().Format(time.RFC3339), Findings: []Finding{}, Stats: []KV{}}
}

func (r *Report) add(sev, id, cat, title, ev, fix string) {
	r.Findings = append(r.Findings, Finding{ID: id, Severity: sev, Title: title, Evidence: ev, Fix: fix, Category: cat})
}

func (r *Report) fact(k, v string) { r.Stats = append(r.Stats, KV{k, v}) }

func (r *Report) finalize() {
	sort.SliceStable(r.Findings, func(i, j int) bool { return sevRank[r.Findings[i].Severity] > sevRank[r.Findings[j].Severity] })
	score := 100
	for _, f := range r.Findings {
		score -= map[string]int{SevCritical: 50, SevHigh: 25, SevMedium: 10, SevLow: 3}[f.Severity]
	}
	r.Score = max(score, 0)
	r.Grade = "F"
	switch {
	case r.Score >= 97:
		r.Grade = "A+"
	case r.Score >= 90:
		r.Grade = "A"
	case r.Score >= 80:
		r.Grade = "B"
	case r.Score >= 65:
		r.Grade = "C"
	case r.Score >= 50:
		r.Grade = "D"
	}
	w := ""
	for _, f := range r.Findings {
		if sevRank[f.Severity] > sevRank[w] {
			w = f.Severity
		}
	}
	switch w {
	case SevCritical:
		r.Verdict = "REJECT — a relying party must not accept this"
	case SevHigh:
		r.Verdict = "REJECT unless the policy explicitly allows it"
	case SevMedium:
		r.Verdict = "ACCEPTABLE with caveats"
	default:
		r.Verdict = "ACCEPT"
	}
}

// ====================================================================
//  VERIFICATION POLICY / INPUTS
// ====================================================================

type checkOpts struct {
	origin      string // expected origin (exact)
	rpID        string // expected RP ID ("" = derive from origin)
	challenge   []byte // expected challenge (nil = not checked)
	prevCount   uint32
	requireUV   bool
	deviceBound bool // reject synced (backup-eligible) credentials
	credKey     *COSEKey
	roots       []*x509.Certificate
}

// decodeB64 accepts base64url / std, padded or not.
func decodeB64(s string) ([]byte, error) {
	s = strings.TrimSpace(s)
	for _, enc := range []*base64.Encoding{base64.RawURLEncoding, base64.URLEncoding, base64.RawStdEncoding, base64.StdEncoding} {
		if b, err := enc.DecodeString(s); err == nil {
			return b, nil
		}
	}
	return nil, errors.New("not base64 / base64url")
}

// loadBytes reads a file, or decodes hex / base64 given inline.
func loadBytes(s string) ([]byte, error) {
	s = strings.TrimSpace(s)
	if s == "" {
		return nil, errors.New("empty input")
	}
	if data, err := os.ReadFile(s); err == nil {
		t := bytes.TrimSpace(data)
		if isText(t) { // a file holding hex / base64 text
			if b, err := decodeText(string(t)); err == nil {
				return b, nil
			}
		}
		return data, nil
	}
	return decodeText(s)
}

func isText(b []byte) bool {
	for _, c := range b {
		if c < 0x20 && c != '\n' && c != '\r' && c != '\t' || c > 0x7e {
			return false
		}
	}
	return len(b) > 0
}

func decodeText(s string) ([]byte, error) {
	c := strings.Map(func(r rune) rune {
		if r == ' ' || r == '\n' || r == '\r' || r == '\t' || r == ':' {
			return -1
		}
		return r
	}, s)
	if b, err := hex.DecodeString(c); err == nil && len(c)%2 == 0 {
		return b, nil
	}
	if b, err := decodeB64(c); err == nil {
		return b, nil
	}
	return nil, errors.New("not a file, hex, or base64 value")
}

// credResponse is the JSON a browser returns (PublicKeyCredential.toJSON()).
type credResponse struct {
	ID       string `json:"id"`
	RawID    string `json:"rawId"`
	Type     string `json:"type"`
	Response struct {
		ClientDataJSON    string   `json:"clientDataJSON"`
		AttestationObject string   `json:"attestationObject"`
		AuthenticatorData string   `json:"authenticatorData"`
		Signature         string   `json:"signature"`
		UserHandle        string   `json:"userHandle"`
		Transports        []string `json:"transports"`
	} `json:"response"`
	AuthenticatorAttachment string `json:"authenticatorAttachment"`
}

type ceremony struct {
	kind       string // registration | authentication
	attObj     []byte
	authData   []byte
	clientData []byte
	signature  []byte
	credID     []byte
	userHandle []byte
	transports []string
}

func parseResponseJSON(data []byte) (*ceremony, error) {
	var cr credResponse
	if err := json.Unmarshal(data, &cr); err != nil {
		return nil, fmt.Errorf("response JSON: %v", err)
	}
	c := &ceremony{transports: cr.Response.Transports}
	var err error
	dec := func(s, what string) []byte {
		if s == "" || err != nil {
			return nil
		}
		var b []byte
		if b, err = decodeB64(s); err != nil {
			err = fmt.Errorf("%s: %v", what, err)
		}
		return b
	}
	c.clientData = dec(cr.Response.ClientDataJSON, "clientDataJSON")
	c.attObj = dec(cr.Response.AttestationObject, "attestationObject")
	c.authData = dec(cr.Response.AuthenticatorData, "authenticatorData")
	c.signature = dec(cr.Response.Signature, "signature")
	c.userHandle = dec(cr.Response.UserHandle, "userHandle")
	c.credID = dec(defaultStr(cr.RawID, cr.ID), "rawId")
	if err != nil {
		return nil, err
	}
	switch {
	case c.attObj != nil:
		c.kind = "registration"
	case c.authData != nil && c.signature != nil:
		c.kind = "authentication"
	default:
		return nil, errors.New("JSON has neither response.attestationObject nor authenticatorData + signature")
	}
	if c.clientData == nil {
		return nil, errors.New("response.clientDataJSON missing")
	}
	return c, nil
}

func defaultStr(s, d string) string {
	if s == "" {
		return d
	}
	return s
}

// loadCredentialKey accepts a COSE key, a PEM / DER SPKI public key, a
// registration response JSON or an attestation object.
func loadCredentialKey(s string) (*COSEKey, error) {
	data, err := os.ReadFile(s)
	t := data
	if err != nil {
		if t, err = decodeText(s); err != nil {
			return nil, err
		}
	} else if tt := bytes.TrimSpace(data); isText(tt) {
		t = tt // trim only text files — decoded binary keys may end in 0x20 / 0x0a
	}
	if blk, _ := pem.Decode(t); blk != nil {
		pub, err := x509.ParsePKIXPublicKey(blk.Bytes)
		if err != nil {
			if c, err2 := x509.ParseCertificate(blk.Bytes); err2 == nil {
				pub = c.PublicKey
			} else {
				return nil, err
			}
		}
		return coseFromCrypto(pub, 0), nil
	}
	if len(t) > 0 && t[0] == '{' {
		c, err := parseResponseJSON(t)
		if err != nil {
			return nil, err
		}
		if c.kind != "registration" {
			return nil, errors.New("--credential JSON must be a registration response")
		}
		t = c.attObj
	} else if isText(t) {
		if b, err := decodeText(string(t)); err == nil {
			t = b
		}
	}
	if v, err := decodeCBOR(t); err == nil && v.Type == cborMap {
		if _, ok := v.mapGetString("authData"); ok {
			ao, err := parseAttestationObject(t)
			if err != nil {
				return nil, err
			}
			if ao.AuthData.Attested == nil {
				return nil, errors.New("attestation object carries no credential key")
			}
			return ao.AuthData.Attested.Key, nil
		}
		return parseCOSEKey(t)
	}
	if pub, err := x509.ParsePKIXPublicKey(t); err == nil {
		return coseFromCrypto(pub, 0), nil
	}
	return nil, errors.New("not a COSE key, PEM/DER public key, attestation object or registration JSON")
}

func loadRoots(path string) ([]*x509.Certificate, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var out []*x509.Certificate
	for {
		var blk *pem.Block
		blk, data = pem.Decode(data)
		if blk == nil {
			break
		}
		if c, err := x509.ParseCertificate(blk.Bytes); err == nil {
			out = append(out, c)
		}
	}
	if len(out) == 0 {
		if c, err := x509.ParseCertificate(data); err == nil {
			out = append(out, c)
		}
	}
	if len(out) == 0 {
		return nil, errors.New("no certificates in " + path)
	}
	return out, nil
}

// ====================================================================
//  CLIENT DATA + RP ID
// ====================================================================

func checkClientData(r *Report, raw []byte, wantType string, o checkOpts) map[string]any {
	var m map[string]any
	if err := json.Unmarshal(raw, &m); err != nil {
		r.add(SevCritical, "OFIDO-CD-000", "clientData", "clientDataJSON is not valid JSON", err.Error(), "")
		return nil
	}
	typ, _ := m["type"].(string)
	origin, _ := m["origin"].(string)
	chal, _ := m["challenge"].(string)
	r.fact("clientData.type", typ)
	r.fact("clientData.origin", origin)
	if typ != wantType {
		r.add(SevCritical, "OFIDO-CD-001", "clientData", "clientData.type is not "+wantType, fmt.Sprintf("got %q", typ),
			"A registration must be webauthn.create and a login webauthn.get — reject cross-ceremony replays.")
	}
	switch {
	case o.origin != "" && origin != o.origin:
		r.add(SevCritical, "OFIDO-CD-002", "clientData", "Origin does not match the expected origin",
			fmt.Sprintf("got %q, expected %q", origin, o.origin), "Compare the origin exactly against an allow-list; this is the phishing defence.")
	case o.origin == "":
		r.add(SevInfo, "OFIDO-CD-002", "clientData", "Origin not checked (pass --origin)", origin, "")
	}
	if u, err := url.Parse(origin); err == nil && u.Scheme == "http" && u.Hostname() != "localhost" && u.Hostname() != "127.0.0.1" {
		r.add(SevHigh, "OFIDO-CD-003", "clientData", "Insecure http: origin", origin, "WebAuthn requires a secure context; serve the RP over HTTPS.")
	}
	cb, err := decodeB64(chal)
	switch {
	case chal == "" || err != nil:
		r.add(SevCritical, "OFIDO-CD-004", "clientData", "clientData.challenge missing or not base64url", chal, "")
	default:
		r.fact("challenge", fmt.Sprintf("%d bytes", len(cb)))
		if o.challenge != nil && !bytes.Equal(cb, o.challenge) {
			r.add(SevCritical, "OFIDO-CD-005", "clientData", "Challenge does not match the one the server issued",
				"possible replay or a response for another session", "Bind each challenge to the session and accept it once.")
		} else if o.challenge == nil {
			r.add(SevInfo, "OFIDO-CD-005", "clientData", "Challenge not compared (pass --challenge)", "", "")
		}
		switch {
		case len(cb) < 16:
			r.add(SevHigh, "OFIDO-CHAL-001", "challenge", "Challenge shorter than 16 bytes", fmt.Sprintf("%d bytes", len(cb)), "Use ≥ 16 (ideally 32) bytes from a CSPRNG.")
		case shannonBits(cb) < 3.0 && len(cb) >= 16:
			r.add(SevHigh, "OFIDO-CHAL-002", "challenge", "Challenge has low entropy", fmt.Sprintf("%.2f bits/byte", shannonBits(cb)), "Generate challenges with crypto/rand, never counters or timestamps.")
		}
	}
	if co, ok := m["crossOrigin"].(bool); ok && co {
		r.add(SevMedium, "OFIDO-CD-006", "clientData", "crossOrigin=true (ceremony ran in a cross-origin iframe)", fmt.Sprint(m["topOrigin"]),
			"Only accept cross-origin ceremonies from allow-listed top origins.")
	}
	if tb, ok := m["tokenBinding"].(map[string]any); ok && tb["status"] == "present" {
		r.fact("tokenBinding", "present")
	}
	return m
}

func shannonBits(b []byte) float64 {
	var f [256]float64
	for _, c := range b {
		f[c]++
	}
	e := 0.0
	for _, c := range f {
		if c > 0 {
			p := c / float64(len(b))
			e -= p * math.Log2(p)
		}
	}
	return e
}

// checkRPID compares rpIdHash with the expected RP ID, or with the origin's
// host and each parent domain when no RP ID was given.
func checkRPID(r *Report, ad *AuthData, o checkOpts, origin string) {
	h := func(s string) []byte { x := sha256.Sum256([]byte(s)); return x[:] }
	if o.rpID != "" {
		if !bytes.Equal(ad.RPIDHash, h(o.rpID)) {
			r.add(SevCritical, "OFIDO-RPID-001", "authData", "rpIdHash does not match the RP ID",
				fmt.Sprintf("rpIdHash %s ≠ SHA-256(%q)", hex.EncodeToString(ad.RPIDHash)[:16]+"…", o.rpID),
				"The credential was scoped to another relying party — reject it.")
			return
		}
		r.fact("rpId", o.rpID+" ✔")
		return
	}
	u, err := url.Parse(origin)
	if err != nil || u.Hostname() == "" {
		r.add(SevInfo, "OFIDO-RPID-002", "authData", "rpIdHash not checked (pass --rpid or --origin)", hex.EncodeToString(ad.RPIDHash), "")
		return
	}
	labels := strings.Split(u.Hostname(), ".")
	for i := 0; i < len(labels)-1 || i == 0 && len(labels) == 1; i++ {
		cand := strings.Join(labels[i:], ".")
		if bytes.Equal(ad.RPIDHash, h(cand)) {
			r.fact("rpId", cand+" ✔ (derived from origin)")
			return
		}
	}
	r.add(SevCritical, "OFIDO-RPID-001", "authData", "rpIdHash matches neither the origin host nor any parent domain",
		hex.EncodeToString(ad.RPIDHash)[:16]+"… vs "+u.Hostname(), "The RP ID must be the origin's host or a registrable suffix of it.")
}

// ====================================================================
//  AUTHENTICATOR DATA CHECKS
// ====================================================================

func checkAuthData(r *Report, ad *AuthData, kind string, o checkOpts) {
	f := ad.Flags
	r.fact("flags", f.String())
	r.fact("signCount", strconv.FormatUint(uint64(ad.SignCount), 10))
	if !f.UP {
		r.add(SevHigh, "OFIDO-AD-001", "authData", "User Present (UP) flag not set", f.String(), "Reject unless the ceremony was explicitly a silent (conditional) one.")
	}
	if !f.UV {
		sev := SevMedium
		if o.requireUV {
			sev = SevHigh
		}
		r.add(sev, "OFIDO-AD-002", "authData", "User Verification (UV) flag not set", f.String(), "Request userVerification: 'required' for passwordless or privileged logins.")
	}
	if f.BS && !f.BE {
		r.add(SevHigh, "OFIDO-AD-003", "authData", "Backup State set without Backup Eligible", f.String(), "Invalid flag combination — reject.")
	}
	if f.Raw&0x22 != 0 {
		r.add(SevLow, "OFIDO-AD-004", "authData", "Reserved flag bits set", fmt.Sprintf("0x%02x", f.Raw&0x22), "")
	}
	if f.BE {
		state := "not yet synced"
		if f.BS {
			state = "synced / backed up"
		}
		r.fact("credential", "multi-device passkey ("+state+")")
		if o.deviceBound {
			r.add(SevHigh, "OFIDO-AD-005", "policy", "Synced passkey where policy requires a device-bound credential", f.String(),
				"Require an authenticator whose credentials are not backup-eligible (hardware security key).")
		}
	} else {
		r.fact("credential", "device-bound")
	}
	if kind == "registration" && !f.AT {
		r.add(SevCritical, "OFIDO-AD-006", "authData", "Registration without attested credential data (AT)", f.String(), "")
	}
	if kind == "authentication" && f.AT {
		r.add(SevMedium, "OFIDO-AD-007", "authData", "Attested credential data inside an assertion", f.String(), "Assertions must not carry AT; reject malformed responses.")
	}
	switch {
	case ad.SignCount == 0 && o.prevCount == 0:
		if !f.BE {
			r.fact("signCount note", "0 — authenticator has no counter (clone detection unavailable)")
		}
	case kind == "authentication" && o.prevCount > 0 && ad.SignCount <= o.prevCount: // a stored counter only applies to logins
		r.add(SevCritical, "OFIDO-AD-010", "authData", "signCount did not increase — possible cloned authenticator",
			fmt.Sprintf("stored %d, received %d", o.prevCount, ad.SignCount), "Flag the credential, require re-registration and investigate.")
	}
	if len(ad.Extensions) > 0 {
		v, err := decodeCBOR(ad.Extensions)
		if err != nil || v.Type != cborMap {
			r.add(SevMedium, "OFIDO-EXT-001", "extensions", "Extension output is not a CBOR map", fmt.Sprint(err), "")
		} else {
			for _, p := range v.Pairs {
				name, _ := p.K.asText()
				val := trunc(p.V.pretty(0), 40)
				if name == "credProtect" {
					if n, ok := p.V.asInt(); ok {
						val = map[int64]string{1: "1 userVerificationOptional", 2: "2 userVerificationOptionalWithCredentialIDList", 3: "3 userVerificationRequired"}[n]
					}
				}
				if _, ok := webauthnExtensions[name]; !ok {
					r.add(SevLow, "OFIDO-EXT-010", "extensions", "Unknown extension output: "+name, val, "")
				}
				r.fact("ext."+name, val)
			}
		}
	}
	if ad.Attested != nil {
		a := ad.Attested
		r.fact("aaguid", canonAAGUID(a.AAGUID))
		if info, ok := lookupAAGUID(a.AAGUID); ok {
			r.fact("authenticator", fmt.Sprintf("%s (%s)", info.Name, defaultStr(info.Source, "built-in")))
			if badStatus[info.Status] {
				r.add(SevCritical, "OFIDO-MDS-001", "metadata", "Authenticator model has status "+info.Status+" in the FIDO MDS",
					info.Name, "Do not accept new registrations from this model; review existing ones.")
			} else if info.Status != "" {
				r.fact("mds status", info.Status)
			}
		} else if bytes.Equal(a.AAGUID, make([]byte, 16)) {
			r.fact("authenticator", "AAGUID all zero (anonymised / U2F / attestation none)")
		} else {
			r.add(SevInfo, "OFIDO-AAGUID-001", "metadata", "AAGUID not in the loaded metadata", canonAAGUID(a.AAGUID), "Load the FIDO MDS3 blob with --mds to identify the model.")
		}
		r.fact("credentialId", fmt.Sprintf("%d bytes", len(a.CredID)))
		if len(a.CredID) < 16 {
			r.add(SevMedium, "OFIDO-CRED-001", "credential", "Credential ID shorter than 16 bytes", fmt.Sprintf("%d bytes", len(a.CredID)), "Short IDs may be guessable or collide.")
		}
		k := a.Key
		for _, kv := range k.summarize() {
			r.fact("key."+kv.K, kv.V)
		}
		if k.Err != "" {
			r.add(SevHigh, "OFIDO-COSE-000", "cose", "Credential public key is not usable", k.Err, "Reject registrations whose key cannot be verified.")
		}
		switch coseAlgDB[k.Alg].Status {
		case "legacy-u2f":
			r.add(SevHigh, "OFIDO-COSE-001", "cose", "Legacy SHA-1 algorithm "+algName(k.Alg), "", "Exclude RS1 from pubKeyCredParams.")
		case "not-for-webauthn":
			r.add(SevMedium, "OFIDO-COSE-002", "cose", algName(k.Alg)+" is not a WebAuthn algorithm", "", "")
		case "":
			r.add(SevMedium, "OFIDO-COSE-003", "cose", "Unknown COSE algorithm", strconv.FormatInt(k.Alg, 10), "")
		}
		if k.Kty == 3 && new(big.Int).SetBytes(k.N).BitLen() < 2048 {
			r.add(SevHigh, "OFIDO-COSE-004", "cose", "RSA credential key shorter than 2048 bits", strconv.Itoa(new(big.Int).SetBytes(k.N).BitLen()), "")
		}
		if a.Key.Alg != 0 && coseAlgDB[a.Key.Alg].KeyType != "" && coseAlgDB[a.Key.Alg].KeyType != coseKtyNames[a.Key.Kty] {
			r.add(SevHigh, "OFIDO-COSE-005", "cose", "COSE alg does not fit the key type", algName(a.Key.Alg)+" on "+coseKtyNames[a.Key.Kty], "")
		}
	}
}

// ====================================================================
//  ATTESTATION
// ====================================================================

type AttestationObject struct {
	Fmt      string
	AuthData *AuthData
	AttStmt  cborValue
}

func parseAttestationObject(b []byte) (*AttestationObject, error) {
	v, err := decodeCBOR(b)
	if err != nil {
		return nil, err
	}
	if v.Type != cborMap {
		return nil, errors.New("attestation object must be a CBOR map")
	}
	ao := &AttestationObject{}
	fv, ok := v.mapGetString("fmt")
	if !ok {
		return nil, errors.New("attestation object has no fmt")
	}
	ao.Fmt, _ = fv.asText()
	av, ok := v.mapGetString("authData")
	bs, ok2 := av.asBytes()
	if !ok || !ok2 {
		return nil, errors.New("attestation object has no authData byte string")
	}
	if ao.AuthData, err = parseAuthData(bs); err != nil {
		return nil, err
	}
	if sv, ok := v.mapGetString("attStmt"); ok {
		ao.AttStmt = sv
	}
	return ao, nil
}

func stmtBytes(s cborValue, k string) []byte {
	if v, ok := s.mapGetString(k); ok {
		b, _ := v.asBytes()
		return b
	}
	return nil
}

func stmtInt(s cborValue, k string) (int64, bool) {
	if v, ok := s.mapGetString(k); ok {
		return v.asInt()
	}
	return 0, false
}

func stmtX5C(s cborValue) ([]*x509.Certificate, error) {
	v, ok := s.mapGetString("x5c")
	if !ok {
		return nil, nil
	}
	if v.Type != cborArray || len(v.Items) == 0 {
		return nil, errors.New("x5c is not a non-empty array")
	}
	var out []*x509.Certificate
	for i, it := range v.Items {
		b, ok := it.asBytes()
		if !ok {
			return nil, fmt.Errorf("x5c[%d] is not a byte string", i)
		}
		c, err := x509.ParseCertificate(b)
		if err != nil {
			return nil, fmt.Errorf("x5c[%d]: %v", i, err)
		}
		out = append(out, c)
	}
	return out, nil
}

var (
	oidFIDOAAGUID   = asn1.ObjectIdentifier{1, 3, 6, 1, 4, 1, 45724, 1, 1, 4}
	oidAppleNonce   = asn1.ObjectIdentifier{1, 2, 840, 113635, 100, 8, 2}
	oidAndroidKey   = asn1.ObjectIdentifier{1, 3, 6, 1, 4, 1, 11129, 2, 1, 17}
	oidTCGKpAIKCert = asn1.ObjectIdentifier{2, 23, 133, 8, 3}
)

func certExt(c *x509.Certificate, oid asn1.ObjectIdentifier) []byte {
	for _, e := range c.Extensions {
		if e.Id.Equal(oid) {
			return e.Value
		}
	}
	return nil
}

// checkChain verifies x5c[i] is signed by x5c[i+1] and, with roots (from
// --roots or the MDS entry), that the chain ends in a trusted root.
func checkChain(r *Report, chain []*x509.Certificate, roots []*x509.Certificate) {
	now := time.Now()
	for i, c := range chain {
		if now.After(c.NotAfter) {
			r.add(SevMedium, "OFIDO-X509-002", "x509", fmt.Sprintf("x5c[%d] has expired", i), c.Subject.CommonName+" · "+c.NotAfter.Format("2006-01-02"),
				"Attestation certificates may outlive the device; check the RP's policy for expired attestation.")
		}
		if i+1 < len(chain) {
			if err := c.CheckSignatureFrom(chain[i+1]); err != nil {
				r.add(SevCritical, "OFIDO-X509-003", "x509", fmt.Sprintf("x5c[%d] is not signed by x5c[%d]", i, i+1), err.Error(), "Broken chain — reject.")
			}
		}
	}
	if len(roots) == 0 {
		r.add(SevLow, "OFIDO-X509-004", "x509", "Attestation chain not anchored (no trust roots)", chain[len(chain)-1].Issuer.CommonName,
			"Pass --roots PEM or --mds BLOB to check the chain against the vendor's attestation roots.")
		return
	}
	pool, inter := x509.NewCertPool(), x509.NewCertPool()
	for _, rt := range roots {
		pool.AddCert(rt)
	}
	for _, c := range chain[1:] {
		inter.AddCert(c)
	}
	// Validate at an instant every certificate is valid (expiry is reported
	// above): Android Keystore leaves start in 1970, long before their CAs.
	at := chain[0].NotBefore
	for _, c := range chain {
		if c.NotBefore.After(at) {
			at = c.NotBefore
		}
	}
	at = at.Add(time.Second)
	_, err := chain[0].Verify(x509.VerifyOptions{Roots: pool, Intermediates: inter, KeyUsages: []x509.ExtKeyUsage{x509.ExtKeyUsageAny},
		CurrentTime: at})
	if err != nil {
		r.add(SevCritical, "OFIDO-X509-005", "x509", "Attestation chain does not lead to a trusted root", err.Error(), "The authenticator is not who it claims to be — reject.")
		return
	}
	r.fact("chain", fmt.Sprintf("%d cert(s) → trusted root ✔", len(chain)))
}

// verifyAttestation dispatches on fmt and verifies the statement signature.
func verifyAttestation(r *Report, ao *AttestationObject, cdh []byte, o checkOpts) {
	ad := ao.AuthData
	st := ao.AttStmt
	signed := append(append([]byte(nil), ad.Raw...), cdh...)
	ok := func(how string) {
		r.fact("attestation", how+" ✔")
	}
	bad := func(id, what string, err error) {
		r.add(SevCritical, id, "attestation", what, fmt.Sprint(err), "Reject the registration.")
	}
	var credPub crypto.PublicKey
	credAlg := int64(0)
	if ad.Attested != nil && ad.Attested.Key != nil {
		credPub, credAlg = ad.Attested.Key.Pub, ad.Attested.Key.Alg
	}
	roots := o.roots
	if ad.Attested != nil {
		if info, ok := lookupAAGUID(ad.Attested.AAGUID); ok && len(info.Roots) > 0 {
			roots = append(roots, info.Roots...)
		}
	}
	r.fact("format", ao.Fmt)
	switch ao.Fmt {
	case "none":
		if st.Type == cborMap && len(st.Pairs) > 0 {
			r.add(SevMedium, "OFIDO-ATT-001", "attestation", "fmt none with a non-empty attStmt", "", "")
		}
		r.add(SevInfo, "OFIDO-ATT-000", "attestation", "No attestation (fmt none)", "authenticator model unproven",
			"Fine for consumer sign-in; require direct attestation for hardware-assurance tiers.")
	case "packed":
		alg, hasAlg := stmtInt(st, "alg")
		sig := stmtBytes(st, "sig")
		x5c, err := stmtX5C(st)
		switch {
		case !hasAlg || sig == nil:
			bad("OFIDO-ATT-010", "packed attStmt missing alg or sig", nil)
		case err != nil:
			bad("OFIDO-ATT-011", "packed x5c unreadable", err)
		case x5c == nil: // self attestation
			if alg != credAlg {
				r.add(SevCritical, "OFIDO-ATT-012", "attestation", "Self-attestation alg differs from the credential key alg", algName(alg)+" vs "+algName(credAlg), "")
			}
			if err := verifySig(credPub, alg, signed, sig); err != nil {
				bad("OFIDO-ATT-013", "packed self-attestation signature invalid", err)
			} else {
				ok("packed self-attestation signature valid")
				r.add(SevLow, "OFIDO-ATT-014", "attestation", "Self attestation — proves key possession, not the authenticator model", "", "")
			}
		default:
			leaf := x5c[0]
			if err := verifySig(leaf.PublicKey, alg, signed, sig); err != nil {
				bad("OFIDO-ATT-015", "packed attestation signature invalid", err)
			} else {
				ok("packed full attestation signature valid (" + leaf.Subject.CommonName + ")")
			}
			// §8.2.1 certificate requirements
			var issues []string
			if leaf.Version != 3 {
				issues = append(issues, "not X.509 v3")
			}
			if !slicesContains(leaf.Subject.OrganizationalUnit, "Authenticator Attestation") {
				issues = append(issues, "subject OU ≠ \"Authenticator Attestation\"")
			}
			if leaf.IsCA {
				issues = append(issues, "basicConstraints CA=true")
			}
			if len(issues) > 0 {
				r.add(SevMedium, "OFIDO-ATT-016", "x509", "Attestation certificate does not meet the packed profile", strings.Join(issues, "; "), "")
			}
			if ext := certExt(leaf, oidFIDOAAGUID); ext != nil && ad.Attested != nil {
				var v []byte
				if _, err := asn1.Unmarshal(ext, &v); err != nil || !bytes.Equal(v, ad.Attested.AAGUID) {
					r.add(SevCritical, "OFIDO-ATT-017", "attestation", "AAGUID in the certificate differs from authData", hex.EncodeToString(v), "Reject: the attestation belongs to another model.")
				}
			}
			checkChain(r, x5c, roots)
		}
	case "fido-u2f":
		sig := stmtBytes(st, "sig")
		x5c, err := stmtX5C(st)
		switch {
		case err != nil || len(x5c) != 1 || sig == nil:
			bad("OFIDO-ATT-020", "fido-u2f attStmt must hold sig and exactly one certificate", err)
		case ad.Attested == nil || ad.Attested.Key.Kty != 2 || ad.Attested.Key.Crv != 1:
			bad("OFIDO-ATT-021", "fido-u2f requires a P-256 credential key", nil)
		default:
			k := ad.Attested.Key
			msg := []byte{0}
			msg = append(msg, ad.RPIDHash...)
			msg = append(msg, cdh...)
			msg = append(msg, ad.Attested.CredID...)
			msg = append(append(append(msg, 0x04), k.X...), k.Y...)
			if err := verifySig(x5c[0].PublicKey, -7, msg, sig); err != nil {
				bad("OFIDO-ATT-022", "fido-u2f attestation signature invalid", err)
			} else {
				ok("fido-u2f signature valid (" + x5c[0].Subject.CommonName + ")")
			}
			r.add(SevLow, "OFIDO-ATT-023", "attestation", "Legacy FIDO U2F authenticator", "no user verification, no resident keys", "")
			checkChain(r, x5c, roots)
		}
	case "apple":
		x5c, err := stmtX5C(st)
		if err != nil || len(x5c) == 0 {
			bad("OFIDO-ATT-030", "apple attStmt needs an x5c chain", err)
			break
		}
		want := sha256.Sum256(signed)
		var ne struct {
			Nonce []byte `asn1:"tag:1,explicit"`
		}
		ext := certExt(x5c[0], oidAppleNonce)
		if _, err := asn1.Unmarshal(ext, &ne); ext == nil || err != nil || !bytes.Equal(ne.Nonce, want[:]) {
			bad("OFIDO-ATT-031", "apple nonce extension does not match SHA-256(authData‖clientDataHash)", err)
		} else if !sameKey(x5c[0].PublicKey, credPub) {
			bad("OFIDO-ATT-032", "apple certificate key differs from the credential key", nil)
		} else {
			ok("apple anonymous attestation nonce + key match")
		}
		checkChain(r, x5c, roots)
	case "android-key":
		alg, _ := stmtInt(st, "alg")
		sig := stmtBytes(st, "sig")
		x5c, err := stmtX5C(st)
		if err != nil || len(x5c) == 0 || sig == nil {
			bad("OFIDO-ATT-040", "android-key attStmt needs alg, sig and x5c", err)
			break
		}
		if err := verifySig(x5c[0].PublicKey, alg, signed, sig); err != nil {
			bad("OFIDO-ATT-041", "android-key signature invalid", err)
			break
		}
		if !sameKey(x5c[0].PublicKey, credPub) {
			bad("OFIDO-ATT-042", "android-key certificate key differs from the credential key", nil)
			break
		}
		var kd struct {
			AttVersion  int
			AttSecLevel asn1.Enumerated
			KMVersion   int
			KMSecLevel  asn1.Enumerated
			Challenge   []byte
			UniqueID    []byte
			SoftwareEnf asn1.RawValue
			TeeEnforced asn1.RawValue
		}
		ext := certExt(x5c[0], oidAndroidKey)
		if _, err := asn1.Unmarshal(ext, &kd); ext == nil || err != nil {
			bad("OFIDO-ATT-043", "android-key KeyDescription extension unreadable", err)
			break
		}
		if !bytes.Equal(kd.Challenge, cdh) {
			bad("OFIDO-ATT-044", "android-key attestationChallenge ≠ clientDataHash", nil)
			break
		}
		ok("android-key signature, key and challenge valid")
		level := map[asn1.Enumerated]string{0: "Software", 1: "TrustedEnvironment", 2: "StrongBox"}[kd.AttSecLevel]
		r.fact("android security level", level)
		if kd.AttSecLevel == 0 {
			r.add(SevMedium, "OFIDO-ATT-045", "attestation", "Android key is software-backed", "attestationSecurityLevel=Software", "Require TrustedEnvironment or StrongBox for high assurance.")
		}
		checkChain(r, x5c, roots)
	case "tpm":
		verifyTPM(r, ad, st, signed, credPub, roots)
	case "android-safetynet":
		r.add(SevMedium, "OFIDO-ATT-050", "attestation", "android-safetynet attestation is deprecated", "SafetyNet was shut down in 2025", "Treat as unverified; Android now uses android-key.")
	default:
		r.add(SevHigh, "OFIDO-ATT-090", "attestation", "Unknown attestation format", ao.Fmt, "Only accept the formats your RP verifies.")
	}
}

func slicesContains(xs []string, s string) bool {
	for _, x := range xs {
		if x == s {
			return true
		}
	}
	return false
}

// ---- TPM (WebAuthn §8.3) ----

type tpmReader struct {
	b   []byte
	i   int
	err error
}

func (t *tpmReader) u16() int {
	if t.err != nil || t.i+2 > len(t.b) {
		t.err = errors.New("TPM structure truncated")
		return 0
	}
	v := int(binary.BigEndian.Uint16(t.b[t.i:]))
	t.i += 2
	return v
}

func (t *tpmReader) u32() uint32 {
	if t.err != nil || t.i+4 > len(t.b) {
		t.err = errors.New("TPM structure truncated")
		return 0
	}
	v := binary.BigEndian.Uint32(t.b[t.i:])
	t.i += 4
	return v
}

func (t *tpmReader) bytes(n int) []byte {
	if t.err != nil || n < 0 || t.i+n > len(t.b) {
		t.err = errors.New("TPM structure truncated")
		return nil
	}
	v := t.b[t.i : t.i+n]
	t.i += n
	return v
}

func (t *tpmReader) sized() []byte { return t.bytes(t.u16()) }

var tpmHash = map[int]crypto.Hash{0x0004: crypto.SHA1, 0x000B: crypto.SHA256, 0x000C: crypto.SHA384, 0x000D: crypto.SHA512}

// tpmPublicKey reads TPMT_PUBLIC (RSA / ECC) into a crypto key.
func tpmPublicKey(pub []byte) (crypto.PublicKey, int, error) {
	t := &tpmReader{b: pub}
	typ := t.u16()
	nameAlg := t.u16()
	t.u32()   // objectAttributes
	t.sized() // authPolicy
	switch typ {
	case 0x0001: // RSA
		t.u16() // symmetric
		t.u16() // scheme
		bits := t.u16()
		exp := t.u32()
		n := t.sized()
		if t.err != nil {
			return nil, 0, t.err
		}
		if exp == 0 {
			exp = 65537
		}
		_ = bits
		return &rsa.PublicKey{N: new(big.Int).SetBytes(n), E: int(exp)}, nameAlg, nil
	case 0x0023: // ECC
		t.u16() // symmetric
		t.u16() // scheme
		curveID := t.u16()
		t.u16() // kdf
		x, y := t.sized(), t.sized()
		if t.err != nil {
			return nil, 0, t.err
		}
		curve := map[int]elliptic.Curve{3: elliptic.P256(), 4: elliptic.P384(), 5: elliptic.P521()}[curveID]
		if curve == nil {
			return nil, 0, fmt.Errorf("unsupported TPM curve 0x%04x", curveID)
		}
		return &ecdsa.PublicKey{Curve: curve, X: new(big.Int).SetBytes(x), Y: new(big.Int).SetBytes(y)}, nameAlg, nil
	}
	return nil, 0, fmt.Errorf("unsupported TPM key type 0x%04x", typ)
}

func verifyTPM(r *Report, ad *AuthData, st cborValue, signed []byte, credPub crypto.PublicKey, roots []*x509.Certificate) {
	bad := func(id, what string, err error) {
		r.add(SevCritical, id, "attestation", what, fmt.Sprint(err), "Reject the registration.")
	}
	ver, _ := st.mapGetString("ver")
	if s, _ := ver.asText(); s != "2.0" {
		bad("OFIDO-TPM-001", "tpm attStmt ver must be \"2.0\"", nil)
		return
	}
	alg, _ := stmtInt(st, "alg")
	sig, certInfo, pubArea := stmtBytes(st, "sig"), stmtBytes(st, "certInfo"), stmtBytes(st, "pubArea")
	x5c, err := stmtX5C(st)
	if sig == nil || certInfo == nil || pubArea == nil || err != nil || len(x5c) == 0 {
		bad("OFIDO-TPM-002", "tpm attStmt needs alg, sig, certInfo, pubArea and x5c (ECDAA is not supported)", err)
		return
	}
	pk, nameAlg, err := tpmPublicKey(pubArea)
	if err != nil {
		bad("OFIDO-TPM-003", "pubArea unreadable", err)
		return
	}
	if !sameKey(pk, credPub) {
		bad("OFIDO-TPM-004", "pubArea key differs from the credential key", nil)
		return
	}
	t := &tpmReader{b: certInfo}
	magic, typ := t.u32(), t.u16()
	t.sized() // qualifiedSigner
	extra := t.sized()
	t.bytes(17) // clockInfo
	t.bytes(8)  // firmwareVersion
	name := t.sized()
	if t.err != nil {
		bad("OFIDO-TPM-005", "certInfo unreadable", t.err)
		return
	}
	if magic != 0xff544347 || typ != 0x8017 {
		bad("OFIDO-TPM-006", "certInfo is not a TPM_ST_ATTEST_CERTIFY structure", fmt.Errorf("magic 0x%08x type 0x%04x", magic, typ))
		return
	}
	h := coseAlgDB[alg].Hash
	if h == 0 {
		h = crypto.SHA256
	}
	hh := h.New()
	hh.Write(signed)
	if !bytes.Equal(extra, hh.Sum(nil)) {
		bad("OFIDO-TPM-007", "certInfo.extraData ≠ hash(authData‖clientDataHash)", nil)
		return
	}
	nh, ok := tpmHash[nameAlg]
	if !ok || len(name) < 2 {
		bad("OFIDO-TPM-008", "unsupported pubArea nameAlg", nil)
		return
	}
	d := nh.New()
	d.Write(pubArea)
	if int(binary.BigEndian.Uint16(name)) != nameAlg || !bytes.Equal(name[2:], d.Sum(nil)) {
		bad("OFIDO-TPM-009", "certInfo.attested.name does not hash pubArea", nil)
		return
	}
	if err := verifySig(x5c[0].PublicKey, alg, certInfo, sig); err != nil {
		bad("OFIDO-TPM-010", "tpm signature over certInfo invalid", err)
		return
	}
	r.fact("attestation", "tpm certInfo, pubArea and AIK signature valid ✔")
	if !hasEKU(x5c[0], oidTCGKpAIKCert) {
		r.add(SevMedium, "OFIDO-TPM-011", "x509", "AIK certificate lacks the tcg-kp-AIKCertificate EKU", "", "")
	}
	checkChain(r, x5c, roots)
}

func hasEKU(c *x509.Certificate, oid asn1.ObjectIdentifier) bool {
	for _, u := range c.UnknownExtKeyUsage {
		if u.Equal(oid) {
			return true
		}
	}
	return false
}

// ====================================================================
//  CEREMONY AUDITS
// ====================================================================

func auditRegistration(target string, attObj, clientData []byte, o checkOpts) *Report {
	r := newReport(target, "registration")
	defer r.finalize()
	ao, err := parseAttestationObject(attObj)
	if err != nil {
		r.add(SevCritical, "OFIDO-PARSE-001", "parse", "Attestation object does not parse", err.Error(), "")
		return r
	}
	origin := ""
	cdh := []byte(nil)
	if clientData != nil {
		m := checkClientData(r, clientData, "webauthn.create", o)
		origin, _ = m["origin"].(string)
		h := sha256.Sum256(clientData)
		cdh = h[:]
	} else {
		r.add(SevInfo, "OFIDO-CD-007", "clientData", "No clientDataJSON — origin, challenge and attestation signature not checked", "", "Pass --clientdata or a full --response JSON.")
	}
	checkRPID(r, ao.AuthData, o, defaultStr(o.origin, origin))
	checkAuthData(r, ao.AuthData, "registration", o)
	if cdh != nil {
		verifyAttestation(r, ao, cdh, o)
	} else {
		r.fact("format", ao.Fmt)
	}
	return r
}

func auditAuthentication(target string, authData, clientData, sig []byte, o checkOpts) *Report {
	r := newReport(target, "authentication")
	defer r.finalize()
	ad, err := parseAuthData(authData)
	if err != nil {
		r.add(SevCritical, "OFIDO-PARSE-002", "parse", "authenticatorData does not parse", err.Error(), "")
		return r
	}
	origin := ""
	if clientData != nil {
		m := checkClientData(r, clientData, "webauthn.get", o)
		origin, _ = m["origin"].(string)
	}
	checkRPID(r, ad, o, defaultStr(o.origin, origin))
	checkAuthData(r, ad, "authentication", o)
	switch {
	case sig == nil || clientData == nil:
		r.add(SevInfo, "OFIDO-SIG-000", "signature", "Assertion signature not checked", "needs signature + clientDataJSON", "")
	case o.credKey == nil:
		r.add(SevInfo, "OFIDO-SIG-000", "signature", "Assertion signature not checked (no credential key)", fmt.Sprintf("%d-byte signature", len(sig)),
			"Pass --credential with the stored COSE / PEM key or the registration response.")
	case o.credKey.Pub == nil:
		r.add(SevHigh, "OFIDO-SIG-002", "signature", "Stored credential key is unusable", o.credKey.Err, "")
	default:
		h := sha256.Sum256(clientData)
		msg := append(append([]byte(nil), authData...), h[:]...)
		alg := o.credKey.Alg
		if alg == 0 { // PEM keys carry no COSE alg — use the natural one
			alg = map[int64]int64{2: -7, 1: -8, 3: -257}[o.credKey.Kty]
		}
		if err := verifySig(o.credKey.Pub, alg, msg, sig); err != nil {
			r.add(SevCritical, "OFIDO-SIG-001", "signature", "Assertion signature is INVALID", err.Error(), "Reject the login.")
		} else {
			r.fact("signature", algName(alg)+" signature valid ✔")
		}
	}
	return r
}

// ====================================================================
//  RP OPTIONS AUDIT (PublicKeyCredentialCreationOptions / RequestOptions)
// ====================================================================

// optionsDoc accepts the JSON a server sends to the browser: the options
// object itself, or wrapped as {"publicKey": {...}}. Binary fields are
// base64url strings (WebAuthn L3 toJSON form).
func auditOptions(target string, data []byte, o checkOpts) *Report {
	var raw map[string]any
	if err := json.Unmarshal(data, &raw); err != nil {
		r := newReport(target, "options")
		r.add(SevCritical, "OFIDO-OPT-000", "options", "Options are not valid JSON", err.Error(), "")
		r.finalize()
		return r
	}
	if pk, ok := raw["publicKey"].(map[string]any); ok {
		raw = pk
	}
	_, isCreate := raw["pubKeyCredParams"]
	if _, ok := raw["user"]; ok {
		isCreate = true
	}
	kind := "request options"
	if isCreate {
		kind = "creation options"
	}
	r := newReport(target, kind)
	defer r.finalize()
	str := func(m map[string]any, k string) string { s, _ := m[k].(string); return s }
	num := func(m map[string]any, k string) (float64, bool) { f, ok := m[k].(float64); return f, ok }

	// challenge
	ch := str(raw, "challenge")
	cb, err := decodeB64(ch)
	switch {
	case ch == "" || err != nil:
		r.add(SevCritical, "OFIDO-OPT-001", "challenge", "No usable challenge", ch, "Send ≥ 16 random bytes (base64url) per ceremony.")
	default:
		r.fact("challenge", fmt.Sprintf("%d bytes, %.2f bits/byte", len(cb), shannonBits(cb)))
		switch {
		case len(cb) < 16:
			r.add(SevHigh, "OFIDO-OPT-002", "challenge", "Challenge shorter than 16 bytes", fmt.Sprintf("%d bytes", len(cb)), "Use 32 bytes from a CSPRNG.")
		case len(cb) >= 16 && shannonBits(cb) < 3.0:
			r.add(SevHigh, "OFIDO-OPT-003", "challenge", "Challenge looks predictable (low entropy)", fmt.Sprintf("%.2f bits/byte", shannonBits(cb)), "Never derive challenges from counters, timestamps or user data.")
		case len(cb) < 32:
			r.add(SevLow, "OFIDO-OPT-004", "challenge", "Challenge shorter than the recommended 32 bytes", fmt.Sprintf("%d bytes", len(cb)), "")
		}
	}

	// RP ID vs origin
	rpID := str(raw, "rpId")
	if rp, ok := raw["rp"].(map[string]any); ok {
		rpID = str(rp, "id")
		r.fact("rp.name", str(rp, "name"))
		if str(rp, "name") == "" {
			r.add(SevLow, "OFIDO-OPT-010", "rp", "rp.name is empty", "", "Browsers show it in the passkey dialog.")
		}
	}
	r.fact("rpId", defaultStr(rpID, "(not set — defaults to the page origin's host)"))
	if net.ParseIP(rpID) != nil {
		r.add(SevHigh, "OFIDO-OPT-011", "rp", "RP ID is an IP address", rpID, "WebAuthn requires a domain; credentials on IPs break on any address change.")
	}
	if o.origin != "" && rpID != "" {
		if u, err := url.Parse(o.origin); err == nil {
			h := u.Hostname()
			if h != rpID && !strings.HasSuffix(h, "."+rpID) {
				r.add(SevCritical, "OFIDO-OPT-012", "rp", "RP ID is not the origin host or a parent domain of it", rpID+" vs "+h,
					"The browser will refuse the ceremony; fix the rpId.")
			} else if h != rpID {
				r.fact("rpId scope", fmt.Sprintf("%s covers every subdomain of it (%s is one)", rpID, h))
			}
		}
	}

	if isCreate {
		user, _ := raw["user"].(map[string]any)
		uid := str(user, "id")
		ub, err := decodeB64(uid)
		switch {
		case user == nil || uid == "" || err != nil:
			r.add(SevCritical, "OFIDO-OPT-020", "user", "user.id missing or not base64url", uid, "")
		default:
			r.fact("user.id", fmt.Sprintf("%d bytes", len(ub)))
			name, disp := str(user, "name"), str(user, "displayName")
			switch {
			case len(ub) > 64:
				r.add(SevHigh, "OFIDO-OPT-021", "user", "user.id longer than 64 bytes", fmt.Sprintf("%d bytes", len(ub)), "Authenticators may reject it; use a 32–64 byte random handle.")
			case isText(ub) && (strings.Contains(string(ub), "@") || string(ub) == name || string(ub) == disp):
				r.add(SevHigh, "OFIDO-OPT-022", "user", "user.id contains personal data", trunc(string(ub), 40),
					"The user handle is stored on the authenticator and returned without consent — use a random opaque ID, never an email or username.")
			case isText(ub) && regexp.MustCompile(`^\d{1,12}$`).Match(ub):
				r.add(SevMedium, "OFIDO-OPT-023", "user", "user.id is a sequential database number", string(ub), "Sequential handles leak account counts and enable correlation; use random bytes.")
			case len(ub) < 16:
				r.add(SevLow, "OFIDO-OPT-024", "user", "user.id shorter than 16 bytes", fmt.Sprintf("%d bytes", len(ub)), "")
			}
			if name == "" {
				r.add(SevLow, "OFIDO-OPT-025", "user", "user.name is empty", "", "Users cannot tell their passkeys apart.")
			}
		}

		// algorithms
		params, _ := raw["pubKeyCredParams"].([]any)
		var algs []int64
		for _, p := range params {
			pm, _ := p.(map[string]any)
			if t := str(pm, "type"); t != "public-key" {
				r.add(SevMedium, "OFIDO-OPT-030", "algorithms", "pubKeyCredParams entry with type "+strconv.Quote(t), "", "")
			}
			if a, ok := num(pm, "alg"); ok {
				algs = append(algs, int64(a))
			}
		}
		var names []string
		for _, a := range algs {
			names = append(names, algName(a))
		}
		r.fact("algorithms", defaultStr(strings.Join(names, ", "), "(none)"))
		has := func(a int64) bool {
			for _, x := range algs {
				if x == a {
					return true
				}
			}
			return false
		}
		switch {
		case len(algs) == 0:
			r.add(SevHigh, "OFIDO-OPT-031", "algorithms", "pubKeyCredParams is empty", "", "List ES256 (-7), EdDSA (-8) and RS256 (-257).")
		default:
			if has(-65535) {
				r.add(SevHigh, "OFIDO-OPT-032", "algorithms", "RS1 (SHA-1) is allowed", "", "Remove -65535.")
			}
			if !has(-7) {
				r.add(SevMedium, "OFIDO-OPT-033", "algorithms", "ES256 (-7) is not allowed", "most security keys and platforms only do ES256", "Add -7.")
			}
			if !has(-257) {
				r.add(SevLow, "OFIDO-OPT-034", "algorithms", "RS256 (-257) is not allowed", "older Windows Hello (TPM) uses RS256", "")
			}
			for _, a := range algs {
				if _, ok := coseAlgDB[a]; !ok {
					r.add(SevLow, "OFIDO-OPT-035", "algorithms", "Unknown COSE algorithm", strconv.FormatInt(a, 10), "")
				}
			}
			if coseAlgDB[algs[0]].KeyType == "RSA" {
				r.add(SevLow, "OFIDO-OPT-036", "algorithms", "RSA is listed first (most preferred)", algName(algs[0]), "Put ES256 / EdDSA first; RSA keys and signatures are much larger.")
			}
		}

		sel, _ := raw["authenticatorSelection"].(map[string]any)
		uv := defaultStr(str(sel, "userVerification"), "preferred")
		rk := str(sel, "residentKey")
		if rk == "" {
			if b, _ := sel["requireResidentKey"].(bool); b {
				rk = "required"
			} else {
				rk = "discouraged"
			}
		}
		if b, ok := sel["requireResidentKey"].(bool); ok && b != (rk == "required") {
			r.add(SevLow, "OFIDO-OPT-040", "selection", "requireResidentKey contradicts residentKey", fmt.Sprintf("%v vs %s", b, rk), "Set both consistently for older browsers.")
		}
		r.fact("userVerification", uv)
		r.fact("residentKey", rk)
		r.fact("attachment", defaultStr(str(sel, "authenticatorAttachment"), "any"))
		if uv == "discouraged" {
			r.add(SevMedium, "OFIDO-OPT-041", "selection", "userVerification is discouraged", "", "Use 'required' (passwordless) or at least 'preferred'.")
		}
		if rk != "discouraged" && uv != "required" {
			r.add(SevMedium, "OFIDO-OPT-042", "selection", "Discoverable credentials without required user verification",
				"rk="+rk+", uv="+uv, "A usernameless login is a single factor unless UV is required.")
		}
		att := defaultStr(str(raw, "attestation"), "none")
		r.fact("attestation", att)
		switch att {
		case "enterprise":
			r.add(SevMedium, "OFIDO-OPT-043", "attestation", "Enterprise attestation requested", "uniquely identifies the device",
				"Only for managed devices on an RP allow-listed by the vendor / policy.")
		case "indirect":
			r.add(SevLow, "OFIDO-OPT-044", "attestation", "attestation 'indirect' is effectively deprecated", "", "Use 'none' or 'direct'.")
		}
		if ex, _ := raw["excludeCredentials"].([]any); len(ex) == 0 {
			r.add(SevLow, "OFIDO-OPT-045", "registration", "excludeCredentials is empty", "the same authenticator can be registered twice",
				"List the user's existing credential IDs.")
		}
		if exts, _ := raw["extensions"].(map[string]any); exts != nil {
			for k := range exts {
				if _, ok := webauthnExtensions[k]; !ok {
					r.add(SevLow, "OFIDO-OPT-046", "extensions", "Unknown extension requested", k, "")
				}
			}
			if _, ok := exts["credProps"]; !ok {
				r.add(SevInfo, "OFIDO-OPT-047", "extensions", "credProps not requested", "", "Request it to learn whether a passkey is discoverable.")
			}
		}
	} else {
		uv := defaultStr(str(raw, "userVerification"), "preferred")
		r.fact("userVerification", uv)
		if uv == "discouraged" {
			r.add(SevMedium, "OFIDO-OPT-041", "selection", "userVerification is discouraged", "", "")
		}
		allow, _ := raw["allowCredentials"].([]any)
		r.fact("allowCredentials", strconv.Itoa(len(allow)))
		switch {
		case len(allow) == 0:
			r.fact("flow", "discoverable credential (passkey / usernameless)")
		case len(allow) > 64:
			r.add(SevLow, "OFIDO-OPT-050", "request", "allowCredentials lists more than 64 credentials", strconv.Itoa(len(allow)), "Authenticators cap the list; filter per user.")
		default:
			r.add(SevInfo, "OFIDO-OPT-051", "request", "allowCredentials reveals the user's credential IDs before authentication",
				"can enable account enumeration", "Return them only after a user-specific, rate-limited lookup, or use discoverable credentials.")
		}
		if m := str(raw, "mediation"); m != "" {
			r.fact("mediation", m)
		}
	}

	if t, ok := num(raw, "timeout"); ok {
		r.fact("timeout", fmt.Sprintf("%.0f s", t/1000))
		switch {
		case t < 30000:
			r.add(SevLow, "OFIDO-OPT-060", "timeout", "Timeout shorter than 30 s", fmt.Sprintf("%.0f ms", t), "Users with assistive technology need more time (WebAuthn recommends 5–10 min).")
		case t > 600000:
			r.add(SevMedium, "OFIDO-OPT-061", "timeout", "Timeout longer than 10 minutes", fmt.Sprintf("%.0f ms", t), "The challenge should expire with the ceremony; keep it ≤ 10 min.")
		}
	}
	if hints, _ := raw["hints"].([]any); len(hints) > 0 {
		for _, h := range hints {
			if s, _ := h.(string); s != "security-key" && s != "client-device" && s != "hybrid" {
				r.add(SevLow, "OFIDO-OPT-062", "hints", "Unknown hint", fmt.Sprint(h), "")
			}
		}
	}
	return r
}

// ====================================================================
//  CREDENTIAL STORE AUDIT
// ====================================================================

type storedCred struct {
	User, ID, Key, AAGUID, Created, LastUsed, Fmt string
	Count                                         uint64
	BE, BS                                        *bool
}

var credAliases = map[string][]string{
	"user":    {"user", "user_id", "userid", "username", "user_handle", "userhandle", "account", "email"},
	"id":      {"credential_id", "credentialid", "id", "cred_id", "raw_id", "rawid"},
	"key":     {"public_key", "publickey", "credential_public_key", "cose_key", "key", "pubkey"},
	"count":   {"sign_count", "signcount", "counter", "sign_counter"},
	"aaguid":  {"aaguid", "authenticator_aaguid"},
	"created": {"created", "created_at", "registered", "registered_at"},
	"last":    {"last_used", "last_used_at", "lastused", "last_login"},
	"be":      {"backup_eligible", "be", "backupeligible"},
	"bs":      {"backup_state", "bs", "backed_up", "backupstate"},
	"fmt":     {"fmt", "attestation_format", "attestation_fmt"},
}

func loadCredStore(path string) ([]storedCred, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var rows []map[string]string
	t := bytes.TrimSpace(data)
	if len(t) > 0 && t[0] == '[' {
		var arr []map[string]any
		if err := json.Unmarshal(t, &arr); err != nil {
			return nil, fmt.Errorf("credential JSON: %v", err)
		}
		for _, a := range arr {
			m := map[string]string{}
			for k, v := range a {
				switch x := v.(type) {
				case string:
					m[strings.ToLower(k)] = x
				case nil:
				default:
					m[strings.ToLower(k)] = strings.Trim(fmt.Sprint(x), "\"")
				}
			}
			rows = append(rows, m)
		}
	} else {
		rd := csv.NewReader(bytes.NewReader(data))
		rd.FieldsPerRecord = -1
		recs, err := rd.ReadAll()
		if err != nil || len(recs) < 2 {
			return nil, fmt.Errorf("credential CSV needs a header row and data (%v)", err)
		}
		for _, rec := range recs[1:] {
			m := map[string]string{}
			for i, h := range recs[0] {
				if i < len(rec) {
					m[strings.ToLower(strings.TrimSpace(h))] = strings.TrimSpace(rec[i])
				}
			}
			rows = append(rows, m)
		}
	}
	get := func(m map[string]string, k string) string {
		for _, a := range credAliases[k] {
			if v, ok := m[a]; ok {
				return v
			}
		}
		return ""
	}
	boolp := func(s string) *bool {
		switch strings.ToLower(s) {
		case "1", "true", "yes", "t":
			b := true
			return &b
		case "0", "false", "no", "f":
			b := false
			return &b
		}
		return nil
	}
	var out []storedCred
	for _, m := range rows {
		c := storedCred{User: get(m, "user"), ID: get(m, "id"), Key: get(m, "key"), AAGUID: get(m, "aaguid"),
			Created: get(m, "created"), LastUsed: get(m, "last"), Fmt: get(m, "fmt"), BE: boolp(get(m, "be")), BS: boolp(get(m, "bs"))}
		c.Count, _ = strconv.ParseUint(get(m, "count"), 10, 64)
		out = append(out, c)
	}
	if len(out) > 0 && out[0].ID == "" && out[0].Key == "" {
		return nil, errors.New("no credential_id / public_key columns found")
	}
	return out, nil
}

func parseDate(s string) (time.Time, bool) {
	for _, l := range []string{time.RFC3339, "2006-01-02 15:04:05", "2006-01-02"} {
		if t, err := time.Parse(l, strings.TrimSpace(s)); err == nil {
			return t, true
		}
	}
	if n, err := strconv.ParseInt(s, 10, 64); err == nil && n > 1e9 {
		if n > 1e12 {
			n /= 1000
		}
		return time.Unix(n, 0), true
	}
	return time.Time{}, false
}

// auditCredStore looks across every stored credential for what a single
// ceremony cannot show: shared keys, duplicate IDs, compromised models,
// lockout-prone users and stale credentials.
func auditCredStore(target string, cs []storedCred) *Report {
	r := newReport(target, "credential store")
	defer r.finalize()
	users := map[string][]int{}
	ids, keys := map[string][]int{}, map[string][]int{}
	algs, models := map[string]int{}, map[string]int{}
	var weak, unusable, shortID, stale, badModel, bigCount []string
	now := time.Now()
	for i, c := range cs {
		users[c.User] = append(users[c.User], i)
		if c.ID != "" {
			ids[c.ID] = append(ids[c.ID], i)
			if b, err := decodeText(c.ID); err == nil && len(b) < 16 {
				shortID = append(shortID, c.User)
			}
		}
		label := fmt.Sprintf("%s/%s", defaultStr(c.User, "?"), trunc(c.ID, 12))
		if c.Key != "" {
			ck, err := loadCredentialKey(c.Key)
			switch {
			case err != nil || ck.Pub == nil:
				unusable = append(unusable, label)
				algs["unusable"]++
			default:
				spki, _ := x509.MarshalPKIXPublicKey(ck.Pub)
				h := sha256.Sum256(spki)
				keys[hex.EncodeToString(h[:])] = append(keys[hex.EncodeToString(h[:])], i)
				name := algName(ck.Alg)
				if ck.Alg == 0 {
					name = coseKtyNames[ck.Kty]
				}
				algs[name]++
				if coseAlgDB[ck.Alg].Status == "legacy-u2f" || ck.Kty == 3 && new(big.Int).SetBytes(ck.N).BitLen() < 2048 {
					weak = append(weak, label+" ("+name+")")
				}
			}
		}
		if c.AAGUID != "" {
			if b, err := hex.DecodeString(strings.ReplaceAll(c.AAGUID, "-", "")); err == nil && len(b) == 16 {
				name := canonAAGUID(b)
				if info, ok := lookupAAGUID(b); ok {
					name = info.Name
					if badStatus[info.Status] {
						badModel = append(badModel, label+" — "+info.Name+" ("+info.Status+")")
					}
				} else if bytes.Equal(b, make([]byte, 16)) {
					name = "(zero AAGUID)"
				}
				models[name]++
			}
		}
		if t, ok := parseDate(c.LastUsed); ok && now.Sub(t) > 365*24*time.Hour {
			stale = append(stale, label)
		}
		if c.Count > 1<<31 {
			bigCount = append(bigCount, fmt.Sprintf("%s=%d", label, c.Count))
		}
	}
	for id, xs := range ids {
		if len(xs) > 1 {
			var us []string
			for _, i := range xs {
				us = append(us, cs[i].User)
			}
			r.add(SevCritical, "OFIDO-STORE-001", "store", "Credential ID stored more than once", trunc(id, 24)+" → "+strings.Join(us, ", "),
				"Credential IDs must be unique; a duplicate lets one authenticator log in as several users.")
		}
	}
	for _, xs := range keys {
		if len(xs) > 1 {
			var us []string
			for _, i := range xs {
				us = append(us, cs[i].User+"/"+trunc(cs[i].ID, 10))
			}
			r.add(SevCritical, "OFIDO-STORE-002", "store", "Same public key behind different credentials", strings.Join(us, ", "),
				"Every credential has its own key pair: a shared key means a cloned / test authenticator or a registration bug.")
		}
	}
	list := func(xs []string) string {
		if len(xs) > 4 {
			return strings.Join(xs[:4], ", ") + fmt.Sprintf(" … +%d", len(xs)-4)
		}
		return strings.Join(xs, ", ")
	}
	if len(badModel) > 0 {
		r.add(SevCritical, "OFIDO-STORE-003", "metadata", fmt.Sprintf("%d credential(s) on models flagged in the FIDO MDS", len(badModel)), list(badModel), "Force re-registration on a different authenticator.")
	}
	if len(weak) > 0 {
		r.add(SevHigh, "OFIDO-STORE-004", "keys", fmt.Sprintf("%d credential(s) with weak keys / algorithms", len(weak)), list(weak), "Ask these users to register a new authenticator.")
	}
	if len(unusable) > 0 {
		r.add(SevHigh, "OFIDO-STORE-005", "keys", fmt.Sprintf("%d stored key(s) cannot be parsed", len(unusable)), list(unusable), "These users cannot log in — check the storage encoding.")
	}
	if len(shortID) > 0 {
		r.add(SevMedium, "OFIDO-STORE-006", "store", fmt.Sprintf("%d credential ID(s) shorter than 16 bytes", len(shortID)), list(shortID), "")
	}
	var lonely []string
	for u, xs := range users {
		if len(xs) != 1 {
			continue
		}
		c := cs[xs[0]]
		if c.BE == nil || !*c.BE {
			lonely = append(lonely, defaultStr(u, "?"))
		}
	}
	sort.Strings(lonely)
	if len(lonely) > 0 {
		r.add(SevMedium, "OFIDO-STORE-007", "recovery", fmt.Sprintf("%d user(s) rely on a single device-bound credential", len(lonely)), list(lonely),
			"Losing that key locks them out: prompt them to add a second authenticator or a synced passkey.")
	}
	if len(stale) > 0 {
		r.add(SevLow, "OFIDO-STORE-008", "hygiene", fmt.Sprintf("%d credential(s) unused for over a year", len(stale)), list(stale), "Review and offer to remove dormant credentials.")
	}
	if len(bigCount) > 0 {
		r.add(SevLow, "OFIDO-STORE-009", "store", "Implausibly large signCount values", list(bigCount), "Check for corrupted counters (clone detection depends on them).")
	}
	syncd := 0
	for _, c := range cs {
		if c.BE != nil && *c.BE {
			syncd++
		}
	}
	r.fact("credentials", strconv.Itoa(len(cs)))
	r.fact("users", strconv.Itoa(len(users)))
	r.fact("synced passkeys", fmt.Sprintf("%d (%.0f%%)", syncd, 100*float64(syncd)/math.Max(1, float64(len(cs)))))
	top := func(m map[string]int) string {
		type kv2 struct {
			k string
			n int
		}
		var xs []kv2
		for k, n := range m {
			xs = append(xs, kv2{k, n})
		}
		sort.Slice(xs, func(i, j int) bool { return xs[i].n > xs[j].n || xs[i].n == xs[j].n && xs[i].k < xs[j].k })
		var p []string
		for i, x := range xs {
			if i == 5 {
				break
			}
			p = append(p, fmt.Sprintf("%s %d", x.k, x.n))
		}
		return strings.Join(p, " · ")
	}
	r.fact("algorithms", top(algs))
	if len(models) > 0 {
		r.fact("authenticators", top(models))
	}
	return r
}

// ====================================================================
//  CTAP2 authenticatorGetInfo
// ====================================================================

var getInfoKeys = map[int64]string{1: "versions", 2: "extensions", 3: "aaguid", 4: "options", 5: "maxMsgSize", 6: "pinUvAuthProtocols",
	7: "maxCredentialCountInList", 8: "maxCredentialIdLength", 9: "transports", 10: "algorithms", 11: "maxSerializedLargeBlobArray",
	12: "forcePINChange", 13: "minPINLength", 14: "firmwareVersion", 15: "maxCredBlobLength", 16: "maxRPIDsForSetMinPINLength",
	17: "preferredPlatformUvAttempts", 18: "uvModality", 19: "certifications", 20: "remainingDiscoverableCredentials",
	21: "vendorPrototypeConfigCommands", 22: "attestationFormats", 23: "uvCountSinceLastPinEntry", 24: "longTouchForReset",
	25: "encIdentifier", 26: "transportsForReset", 27: "pinComplexityPolicy", 28: "pinComplexityPolicyURL", 29: "maxPINLength"}

// auditGetInfo grades an authenticatorGetInfo response (CTAP 2.1 §6.4):
// what the key can enforce (PIN, built-in UV, discoverable credentials).
func auditGetInfo(target string, b []byte) *Report {
	r := newReport(target, "authenticatorGetInfo")
	defer r.finalize()
	if len(b) > 0 && b[0] == 0x00 && len(b) > 1 && b[1]>>5 == 5 {
		b = b[1:] // CTAP status byte (success) in front of the map
	}
	v, err := decodeCBOR(b)
	if err != nil || v.Type != cborMap {
		r.add(SevCritical, "OFIDO-INFO-000", "parse", "Not a getInfo CBOR map", fmt.Sprint(err), "")
		return r
	}
	get := func(k int64) (cborValue, bool) { return v.mapGetInt(k) }
	strs := func(x cborValue) []string {
		var out []string
		for _, it := range x.Items {
			if s, ok := it.asText(); ok {
				out = append(out, s)
			}
		}
		return out
	}
	var versions []string
	if x, ok := get(1); ok {
		versions = strs(x)
	}
	r.fact("versions", strings.Join(versions, ", "))
	hasV := func(s string) bool { return slicesContains(versions, s) }
	switch {
	case len(versions) == 0:
		r.add(SevHigh, "OFIDO-INFO-001", "versions", "No versions reported", "", "")
	case !hasV("FIDO_2_0") && !hasV("FIDO_2_1") && !hasV("FIDO_2_1_PRE") && !hasV("FIDO_2_2"):
		r.add(SevHigh, "OFIDO-INFO-002", "versions", "U2F-only authenticator", strings.Join(versions, ", "), "No user verification or passkeys — FIDO2 is required for passwordless.")
	case !hasV("FIDO_2_1") && !hasV("FIDO_2_2"):
		r.add(SevLow, "OFIDO-INFO-003", "versions", "Pre-CTAP 2.1 authenticator", strings.Join(versions, ", "), "No credential management / minPINLength / alwaysUv on older firmware.")
	}
	if x, ok := get(3); ok {
		if a, ok := x.asBytes(); ok && len(a) == 16 {
			name := "unknown model"
			if info, ok := lookupAAGUID(a); ok {
				name = info.Name
				if badStatus[info.Status] {
					r.add(SevCritical, "OFIDO-INFO-004", "metadata", "Model flagged in the FIDO MDS: "+info.Status, info.Name, "")
				}
			}
			r.fact("aaguid", canonAAGUID(a)+" — "+name)
		}
	}
	opts := map[string]bool{}
	present := map[string]bool{}
	if x, ok := get(4); ok {
		for _, p := range x.Pairs {
			k, _ := p.K.asText()
			present[k] = true
			opts[k] = p.V.Type == cborSimple && p.V.Simple == 21
		}
	}
	var on, off []string
	for _, k := range []string{"plat", "rk", "clientPin", "up", "uv", "pinUvAuthToken", "credMgmt", "bioEnroll", "largeBlobs", "ep", "alwaysUv", "makeCredUvNotRqd", "setMinPINLength", "authnrCfg"} {
		if present[k] {
			if opts[k] {
				on = append(on, k)
			} else {
				off = append(off, k)
			}
		}
	}
	r.fact("options on", strings.Join(on, " "))
	if len(off) > 0 {
		r.fact("options off", strings.Join(off, " "))
	}
	switch {
	case !present["clientPin"] && !present["uv"]:
		r.add(SevHigh, "OFIDO-INFO-010", "uv", "No user verification capability (no PIN, no biometrics)", "", "Cannot satisfy userVerification: required — not suitable for passwordless.")
	case present["clientPin"] && !opts["clientPin"] && !opts["uv"]:
		r.add(SevMedium, "OFIDO-INFO-011", "uv", "PIN supported but not set", "clientPin=false", "Set a PIN, otherwise UV-required logins fail and anyone holding the key passes.")
	}
	if opts["makeCredUvNotRqd"] {
		r.add(SevMedium, "OFIDO-INFO-012", "uv", "Credentials can be created without user verification", "makeCredUvNotRqd=true", "Enable alwaysUv if the key's policy allows it.")
	}
	if opts["alwaysUv"] {
		r.fact("alwaysUv", "every operation needs PIN / biometrics ✔")
	}
	if !opts["rk"] {
		r.add(SevInfo, "OFIDO-INFO-013", "passkeys", "No discoverable credentials (passkeys)", "", "Only second-factor use with allowCredentials.")
	}
	if present["credMgmt"] == false && present["credentialMgmtPreview"] == false && opts["rk"] {
		r.add(SevLow, "OFIDO-INFO-014", "passkeys", "Passkeys without credential management", "", "Users cannot list or delete single passkeys — only a full reset.")
	}
	if opts["ep"] {
		r.fact("enterprise attestation", "enabled")
	}
	if x, ok := get(13); ok {
		if n, ok := x.asInt(); ok {
			r.fact("minPINLength", strconv.FormatInt(n, 10))
			if n < 6 {
				r.add(SevLow, "OFIDO-INFO-020", "pin", "Minimum PIN length below 6", strconv.FormatInt(n, 10), "Raise it with setMinPINLength where policy allows.")
			}
		}
	}
	if x, ok := get(6); ok {
		var ps []string
		two := false
		for _, it := range x.Items {
			n, _ := it.asInt()
			ps = append(ps, strconv.FormatInt(n, 10))
			two = two || n == 2
		}
		r.fact("pinUvAuthProtocols", strings.Join(ps, ", "))
		if !two && len(ps) > 0 {
			r.add(SevLow, "OFIDO-INFO-021", "pin", "Only pinUvAuthProtocol 1", "", "Protocol 2 (HMAC-SHA-256, AES-CBC with random IV) is preferred.")
		}
	}
	if x, ok := get(10); ok {
		var as []string
		for _, it := range x.Items {
			if a, ok := it.mapGetString("alg"); ok {
				n, _ := a.asInt()
				as = append(as, algName(n))
			}
		}
		r.fact("algorithms", strings.Join(as, ", "))
	}
	if x, ok := get(9); ok {
		r.fact("transports", strings.Join(strs(x), ", "))
	}
	if x, ok := get(2); ok {
		r.fact("extensions", strings.Join(strs(x), ", "))
	}
	if x, ok := get(14); ok {
		if n, ok := x.asInt(); ok {
			r.fact("firmwareVersion", fmt.Sprintf("%d (0x%x)", n, n))
		}
	}
	if x, ok := get(20); ok {
		if n, ok := x.asInt(); ok {
			r.fact("free passkey slots", strconv.FormatInt(n, 10))
			if n < 5 {
				r.add(SevLow, "OFIDO-INFO-022", "passkeys", "Almost no room for new passkeys", strconv.FormatInt(n, 10)+" slots left", "")
			}
		}
	}
	if x, ok := get(12); ok && x.Type == cborSimple && x.Simple == 21 {
		r.add(SevMedium, "OFIDO-INFO-023", "pin", "The authenticator demands a PIN change", "forcePINChange=true", "Change the PIN before use.")
	}
	if x, ok := get(19); ok {
		var cs []string
		for _, p := range x.Pairs {
			k, _ := p.K.asText()
			n, _ := p.V.asInt()
			cs = append(cs, fmt.Sprintf("%s %d", k, n))
		}
		r.fact("certifications", strings.Join(cs, ", "))
	}
	return r
}

// demoGetInfo: a CTAP 2.1 security key with a PIN that is not yet set.
func demoGetInfo() []byte {
	ag, _ := hex.DecodeString("2fc0579f811347eab116bb5a8db9202a")
	t, f := cborValue{Type: cborSimple, Simple: 21}, cborValue{Type: cborSimple, Simple: 20}
	arr := func(xs ...cborValue) cborValue { return cborValue{Type: cborArray, Items: xs} }
	return append([]byte{0}, encodeCBOR(cMap(
		cInt(1), arr(cText("U2F_V2"), cText("FIDO_2_0"), cText("FIDO_2_1")),
		cInt(2), arr(cText("credProtect"), cText("hmac-secret"), cText("largeBlobKey"), cText("credBlob"), cText("minPinLength")),
		cInt(3), cBytes(ag),
		cInt(4), cMap(cText("rk"), t, cText("up"), t, cText("plat"), f, cText("alwaysUv"), f, cText("credMgmt"), t,
			cText("authnrCfg"), t, cText("clientPin"), f, cText("largeBlobs"), t, cText("pinUvAuthToken"), t,
			cText("setMinPINLength"), t, cText("makeCredUvNotRqd"), t),
		cInt(6), arr(cInt(2), cInt(1)),
		cInt(9), arr(cText("nfc"), cText("usb")),
		cInt(10), arr(cMap(cText("alg"), cInt(-7), cText("type"), cText("public-key")), cMap(cText("alg"), cInt(-8), cText("type"), cText("public-key"))),
		cInt(13), cInt(4),
		cInt(14), cInt(328707),
		cInt(20), cInt(97),
	))...)
}

// ====================================================================
//  RP TEST GENERATOR — signed good and malicious ceremonies
// ====================================================================

type genCase struct {
	Name     string `json:"name"`
	File     string `json:"file"`
	Ceremony string `json:"ceremony"` // registration | authentication
	Expect   string `json:"expect"`   // accept | reject | reject-if-uv-required
	Why      string `json:"why"`
	OFIDO    string `json:"ofido_verdict"`
}

type genManifest struct {
	Tool          string    `json:"tool"`
	Version       string    `json:"version"`
	Origin        string    `json:"origin"`
	RPID          string    `json:"rp_id"`
	Challenge     string    `json:"challenge"`
	CredentialID  string    `json:"credential_id"`
	UserHandle    string    `json:"user_handle"`
	PublicKeyCOSE string    `json:"credential_public_key_cose"`
	PublicKeyPEM  string    `json:"credential_public_key_pem"`
	StoredCount   uint32    `json:"stored_sign_count"`
	Cases         []genCase `json:"cases"`
}

// genTests writes a valid registration + login and signed variants that a
// correct relying party must reject. Every variant is signed with the real
// key, so only the targeted check can catch it.
func genTests(dir, origin, rpID string, chal []byte) (genManifest, error) {
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return genManifest{}, err
	}
	if rpID == "" {
		u, err := url.Parse(origin)
		if err != nil || u.Hostname() == "" {
			return genManifest{}, errors.New("--gen-tests needs --origin https://host")
		}
		rpID = u.Hostname()
	}
	if chal == nil {
		chal = make([]byte, 32)
		rand.Read(chal)
	}
	key, _ := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	credID := make([]byte, 32)
	rand.Read(credID)
	userHandle := make([]byte, 32)
	rand.Read(userHandle)
	cose := coseOf(&key.PublicKey, -7)
	spki, _ := x509.MarshalPKIXPublicKey(&key.PublicKey)
	const stored = 10
	e := base64.RawURLEncoding.EncodeToString
	m := genManifest{Tool: APPNAME, Version: VERSION, Origin: origin, RPID: rpID, Challenge: e(chal), CredentialID: e(credID),
		UserHandle: e(userHandle), PublicKeyCOSE: e(cose), StoredCount: stored,
		PublicKeyPEM: string(pem.EncodeToMemory(&pem.Block{Type: "PUBLIC KEY", Bytes: spki}))}
	write := func(name, ceremonyKind, expect, why string, body []byte) error {
		f := filepath.Join(dir, name+".json")
		if err := os.WriteFile(f, body, 0o644); err != nil {
			return err
		}
		m.Cases = append(m.Cases, genCase{Name: name, File: filepath.Base(f), Ceremony: ceremonyKind, Expect: expect, Why: why})
		return nil
	}
	resp := func(id, cd, att, ad, sig, uh []byte) []byte {
		r := map[string]any{"clientDataJSON": e(cd)}
		if att != nil {
			r["attestationObject"] = e(att)
		} else {
			r["authenticatorData"], r["signature"] = e(ad), e(sig)
			if uh != nil {
				r["userHandle"] = e(uh)
			}
		}
		b, _ := json.MarshalIndent(map[string]any{"id": e(id), "rawId": e(id), "type": "public-key", "response": r,
			"clientExtensionResults": map[string]any{}}, "", "  ")
		return b
	}
	aaguid := make([]byte, 16)
	// ---- registration ----
	reg := func(name, expect, why string, typ, org string, ch []byte, rp string, flags byte, keyBytes []byte, mutate func(ad []byte) []byte, attMut func(ad []byte, sig []byte) []byte) error {
		cd := clientDataOf(typ, org, ch)
		ad := authDataOf(rp, flags, 0, aaguid, credID, keyBytes)
		if mutate != nil {
			ad = mutate(ad)
		}
		h := sha256.Sum256(cd)
		sig := sign(key, -7, append(append([]byte(nil), ad...), h[:]...))
		att := attObjOf("packed", ad, cMap(cText("alg"), cInt(-7), cText("sig"), cBytes(sig)))
		if attMut != nil {
			att = attMut(ad, sig)
		}
		return write(name, "registration", expect, why, resp(credID, cd, att, nil, nil, nil))
	}
	const ok = 0x45 // UP UV AT
	steps := []func() error{
		func() error {
			return reg("reg-01-valid", "accept", "well-formed packed self-attestation", "webauthn.create", origin, chal, rpID, ok, cose, nil, nil)
		},
		func() error {
			return reg("reg-02-lookalike-origin", "reject", "origin is a look-alike phishing domain", "webauthn.create", strings.Replace(origin, "://", "://login-", 1)+".evil.example", chal, rpID, ok, cose, nil, nil)
		},
		func() error {
			return reg("reg-03-wrong-type", "reject", "clientData.type is webauthn.get", "webauthn.get", origin, chal, rpID, ok, cose, nil, nil)
		},
		func() error {
			other := append([]byte(nil), chal...)
			other[0] ^= 0xFF
			return reg("reg-04-wrong-challenge", "reject", "challenge was never issued (replay)", "webauthn.create", origin, other, rpID, ok, cose, nil, nil)
		},
		func() error {
			return reg("reg-05-other-rpid", "reject", "rpIdHash is for evil.example", "webauthn.create", origin, chal, "evil.example", ok, cose, nil, nil)
		},
		func() error {
			return reg("reg-06-no-user-presence", "reject", "UP flag cleared", "webauthn.create", origin, chal, rpID, 0x44, cose, nil, nil)
		},
		func() error {
			return reg("reg-07-no-user-verification", "reject-if-uv-required", "UV flag cleared", "webauthn.create", origin, chal, rpID, 0x41, cose, nil, nil)
		},
		func() error {
			return reg("reg-08-bs-without-be", "reject", "Backup State set without Backup Eligible", "webauthn.create", origin, chal, rpID, ok|0x10, cose, nil, nil)
		},
		func() error {
			return reg("reg-09-bad-attestation-sig", "reject", "attestation signature does not verify", "webauthn.create", origin, chal, rpID, ok, cose, nil,
				func(ad, sig []byte) []byte {
					s := append([]byte(nil), sig...)
					s[len(s)-1] ^= 1
					return attObjOf("packed", ad, cMap(cText("alg"), cInt(-7), cText("sig"), cBytes(s)))
				})
		},
		func() error {
			return reg("reg-10-alg-mismatch", "reject", "self-attestation alg (-257) differs from the key alg (-7)", "webauthn.create", origin, chal, rpID, ok, cose, nil,
				func(ad, sig []byte) []byte {
					return attObjOf("packed", ad, cMap(cText("alg"), cInt(-257), cText("sig"), cBytes(sig)))
				})
		},
		func() error {
			return reg("reg-11-unknown-fmt", "reject", "attestation format 'owl-custom' is not defined", "webauthn.create", origin, chal, rpID, ok, cose, nil,
				func(ad, sig []byte) []byte {
					return attObjOf("owl-custom", ad, cMap(cText("sig"), cBytes(sig)))
				})
		},
		func() error {
			return reg("reg-12-trailing-bytes", "reject", "authenticatorData has bytes after the COSE key without ED", "webauthn.create", origin, chal, rpID, ok, cose,
				func(ad []byte) []byte { return append(ad, 0xDE, 0xAD) }, nil)
		},
		func() error {
			bad := append([]byte(nil), cose...)
			bad[len(bad)-1] ^= 0x55 // y coordinate no longer on the curve
			return reg("reg-13-invalid-curve-point", "reject", "credential public key is not a point on P-256", "webauthn.create", origin, chal, rpID, ok, bad, nil, nil)
		},
		func() error {
			cd := []byte("not json at all")
			ad := authDataOf(rpID, ok, 0, aaguid, credID, cose)
			att := attObjOf("none", ad, cMap())
			return write("reg-14-clientdata-not-json", "registration", "reject", "clientDataJSON does not parse", resp(credID, cd, att, nil, nil, nil))
		},
	}
	// ---- authentication ----
	login := func(name, expect, why, typ, org string, ch []byte, rp string, flags byte, count uint32, sigMut func([]byte) []byte, id, uh []byte) error {
		cd := clientDataOf(typ, org, ch)
		ad := authDataOf(rp, flags, count, nil, nil, nil)
		h := sha256.Sum256(cd)
		sig := sign(key, -7, append(append([]byte(nil), ad...), h[:]...))
		if sigMut != nil {
			sig = sigMut(sig)
		}
		return write(name, "authentication", expect, why, resp(id, cd, nil, ad, sig, uh))
	}
	steps = append(steps,
		func() error {
			return login("auth-01-valid", "accept", "signCount 11 > stored 10", "webauthn.get", origin, chal, rpID, 0x05, stored+1, nil, credID, userHandle)
		},
		func() error {
			return login("auth-02-bad-signature", "reject", "signature does not verify", "webauthn.get", origin, chal, rpID, 0x05, stored+1,
				func(s []byte) []byte { s = append([]byte(nil), s...); s[8] ^= 1; return s }, credID, userHandle)
		},
		func() error {
			return login("auth-03-counter-regression", "reject", "signCount 5 ≤ stored 10 (cloned authenticator)", "webauthn.get", origin, chal, rpID, 0x05, 5, nil, credID, userHandle)
		},
		func() error {
			return login("auth-04-lookalike-origin", "reject", "look-alike phishing origin", "webauthn.get", strings.Replace(origin, "://", "://login-", 1)+".evil.example", chal, rpID, 0x05, stored+1, nil, credID, userHandle)
		},
		func() error {
			other := append([]byte(nil), chal...)
			other[len(other)-1] ^= 0xFF
			return login("auth-05-wrong-challenge", "reject", "challenge was not issued for this session", "webauthn.get", origin, other, rpID, 0x05, stored+1, nil, credID, userHandle)
		},
		func() error {
			return login("auth-06-create-type", "reject", "clientData.type is webauthn.create", "webauthn.create", origin, chal, rpID, 0x05, stored+1, nil, credID, userHandle)
		},
		func() error {
			return login("auth-07-no-user-presence", "reject", "UP flag cleared", "webauthn.get", origin, chal, rpID, 0x04, stored+1, nil, credID, userHandle)
		},
		func() error {
			return login("auth-08-other-rpid", "reject", "rpIdHash is for evil.example", "webauthn.get", origin, chal, "evil.example", 0x05, stored+1, nil, credID, userHandle)
		},
		func() error {
			return login("auth-09-truncated-signature", "reject", "DER signature cut short", "webauthn.get", origin, chal, rpID, 0x05, stored+1,
				func(s []byte) []byte { return s[:len(s)-10] }, credID, userHandle)
		},
		func() error {
			other := make([]byte, 32)
			rand.Read(other)
			return login("auth-10-unknown-credential", "reject", "rawId is not a registered credential (look it up before verifying)", "webauthn.get", origin, chal, rpID, 0x05, stored+1, nil, other, userHandle)
		},
		func() error {
			other := make([]byte, 32)
			rand.Read(other)
			return login("auth-11-wrong-user-handle", "reject", "userHandle belongs to another account", "webauthn.get", origin, chal, rpID, 0x05, stored+1, nil, credID, other)
		},
		func() error {
			return login("auth-12-no-user-verification", "reject-if-uv-required", "UV flag cleared", "webauthn.get", origin, chal, rpID, 0x01, stored+1, nil, credID, userHandle)
		},
	)
	for _, st := range steps {
		if err := st(); err != nil {
			return m, err
		}
	}
	// cross-check every case with OFIDO itself
	ck, _ := parseCOSEKey(cose)
	o := checkOpts{origin: origin, rpID: rpID, challenge: chal, prevCount: stored, requireUV: true, credKey: ck}
	for i, c := range m.Cases {
		data, _ := os.ReadFile(filepath.Join(dir, c.File))
		cr, err := parseResponseJSON(data)
		if err != nil {
			m.Cases[i].OFIDO = "reject (" + err.Error() + ")"
			continue
		}
		r := auditCeremony(c.File, cr, o)
		v := "accept"
		if strings.HasPrefix(r.Verdict, "REJECT") {
			v = "reject"
		}
		// identity checks are the RP's job, not visible in the ceremony itself
		if c.Name == "auth-10-unknown-credential" && !bytes.Equal(cr.credID, credID) || c.Name == "auth-11-wrong-user-handle" && !bytes.Equal(cr.userHandle, userHandle) {
			v = "reject (credential / user lookup)"
		}
		m.Cases[i].OFIDO = v
	}
	b, _ := json.MarshalIndent(m, "", "  ")
	if err := os.WriteFile(filepath.Join(dir, "manifest.json"), append(b, '\n'), 0o644); err != nil {
		return m, err
	}
	readme := fmt.Sprintf(`OFIDO relying-party test vectors
================================
Origin %s · RP ID %s · challenge (base64url) %s
Registered credential: id %s, user handle %s, stored signCount %d
Public key: manifest.json → credential_public_key_cose / _pem

Feed each JSON to your server's verify endpoint with the values above.
Every file is signed with the real credential key, so only the targeted
check can reject it. "reject-if-uv-required" depends on your UV policy.
manifest.json lists the expected outcome and OFIDO's own verdict.
`, origin, rpID, m.Challenge, m.CredentialID, m.UserHandle, stored)
	return m, os.WriteFile(filepath.Join(dir, "README.txt"), []byte(readme), 0o644)
}

func printGen(dir string, m genManifest) {
	kv("Directory", dir)
	kv("Origin / RP ID", m.Origin+" · "+m.RPID)
	kv("Credential ID", m.CredentialID)
	kv("Stored count", strconv.Itoa(int(m.StoredCount)))
	fmt.Println()
	var rows [][]string
	agree := 0
	for _, c := range m.Cases {
		exp := col(c.Expect, GRN)
		if strings.HasPrefix(c.Expect, "reject") {
			exp = col(c.Expect, R)
		}
		match := strings.HasPrefix(c.OFIDO, strings.TrimSuffix(c.Expect, "-if-uv-required"))
		if match {
			agree++
		}
		mark := col("✔", GRN+B)
		if !match {
			mark = col("✘", R+B)
		}
		rows = append(rows, []string{c.File, exp, mark + " " + trunc(c.OFIDO, 30), trunc(c.Why, 46)})
	}
	table([]string{"FILE", "EXPECT", "OFIDO", "WHY"}, rows)
	fmt.Println()
	okMsg(fmt.Sprintf("%d vectors written; OFIDO agrees on %d/%d", len(m.Cases), agree, len(m.Cases)))
	info("point your server's verify endpoint at each file — anything it accepts that is expected 'reject' is a bug")
}

// ====================================================================
//  OUTPUT
// ====================================================================

func printReport(r *Report) {
	sectionHeader(fmt.Sprintf("WebAuthn %s — %s", r.Kind, r.Target))
	verdict := col(r.Verdict, GRN+B)
	switch {
	case strings.HasPrefix(r.Verdict, "REJECT —"):
		verdict = col(r.Verdict, R+B)
	case strings.HasPrefix(r.Verdict, "REJECT"):
		verdict = col(r.Verdict, R)
	case strings.HasPrefix(r.Verdict, "ACCEPTABLE"):
		verdict = col(r.Verdict, YLW+B)
	}
	kv("Verdict", verdict)
	kv("Grade", gradeColor(r.Grade)+col(fmt.Sprintf("  (score %d/100)", r.Score), DIM))
	for _, f := range r.Stats {
		v := f.V
		if strings.HasSuffix(v, "✔") {
			v = col(v, GRN)
		}
		kv(f.K, trunc(v, 90))
	}
	fmt.Println()
	if len(r.Findings) == 0 {
		okMsg("No findings — the ceremony verifies under the given policy.")
		return
	}
	var rows [][]string
	for _, f := range r.Findings {
		rows = append(rows, []string{sevColor(f.Severity), f.ID, trunc(f.Title, 52), trunc(f.Evidence, 40)})
	}
	table([]string{"SEV", "ID", "FINDING", "EVIDENCE"}, rows)
	seen := map[string]bool{}
	first := true
	for _, f := range r.Findings {
		if f.Fix == "" || seen[f.Fix] || sevRank[f.Severity] < sevRank[SevMedium] {
			continue
		}
		if first {
			fmt.Println()
			first = false
		}
		seen[f.Fix] = true
		fmt.Println("  " + col("→ ", CY) + col(f.Fix, DIM))
	}
}

func render(r *Report, format string) (string, error) {
	switch strings.ToLower(format) {
	case "json":
		b, _ := json.MarshalIndent(r, "", "  ")
		return string(b) + "\n", nil
	case "csv":
		var buf bytes.Buffer
		w := csv.NewWriter(&buf)
		w.Write([]string{"severity", "id", "category", "title", "evidence", "fix"})
		for _, f := range r.Findings {
			w.Write([]string{f.Severity, f.ID, f.Category, f.Title, f.Evidence, f.Fix})
		}
		w.Flush()
		return buf.String(), nil
	case "md", "markdown":
		var b strings.Builder
		fmt.Fprintf(&b, "# %s — WebAuthn %s\n\n- **Target:** %s\n- **Verdict:** %s\n- **Grade:** %s (%d/100)\n\n| Fact | Value |\n|---|---|\n",
			APPNAME, r.Kind, r.Target, r.Verdict, r.Grade, r.Score)
		for _, f := range r.Stats {
			fmt.Fprintf(&b, "| %s | %s |\n", f.K, strings.ReplaceAll(f.V, "|", `\|`))
		}
		b.WriteString("\n| Severity | ID | Finding | Evidence |\n|---|---|---|---|\n")
		for _, f := range r.Findings {
			fmt.Fprintf(&b, "| %s | %s | %s | %s |\n", f.Severity, f.ID, f.Title, strings.ReplaceAll(f.Evidence, "|", `\|`))
		}
		return b.String(), nil
	case "sarif":
		level := map[string]string{SevCritical: "error", SevHigh: "error", SevMedium: "warning", SevLow: "note", SevInfo: "note"}
		var results []map[string]any
		rules := map[string]bool{}
		var rl []map[string]any
		for _, f := range r.Findings {
			if !rules[f.ID] {
				rules[f.ID] = true
				rl = append(rl, map[string]any{"id": f.ID, "shortDescription": map[string]any{"text": f.Title}, "help": map[string]any{"text": defaultStr(f.Fix, f.Title)}})
			}
			results = append(results, map[string]any{"ruleId": f.ID, "level": level[f.Severity],
				"message":   map[string]any{"text": f.Title + " — " + f.Evidence},
				"locations": []any{map[string]any{"logicalLocations": []any{map[string]any{"name": r.Target + "#" + f.Category}}}}})
		}
		if results == nil {
			results = []map[string]any{}
		}
		doc := map[string]any{"$schema": "https://json.schemastore.org/sarif-2.1.0.json", "version": "2.1.0",
			"runs": []any{map[string]any{"tool": map[string]any{"driver": map[string]any{"name": APPNAME, "version": VERSION,
				"informationUri": "https://" + WEBSITE, "rules": rl}}, "results": results}}}
		b, _ := json.MarshalIndent(doc, "", "  ")
		return string(b) + "\n", nil
	case "", "txt", "text":
		var b strings.Builder
		fmt.Fprintf(&b, "%s v%s — WebAuthn %s\nTarget : %s\nVerdict: %s\nGrade  : %s (%d/100)\n%s\n",
			APPNAME, VERSION, r.Kind, r.Target, r.Verdict, r.Grade, r.Score, strings.Repeat("-", 66))
		for _, f := range r.Stats {
			fmt.Fprintf(&b, "%-22s %s\n", f.K, f.V)
		}
		b.WriteString(strings.Repeat("-", 66) + "\n")
		for _, f := range r.Findings {
			fmt.Fprintf(&b, "[%s] %s  %s\n", f.Severity, f.ID, f.Title)
			if f.Evidence != "" {
				fmt.Fprintf(&b, "    evidence: %s\n", f.Evidence)
			}
			if f.Fix != "" {
				fmt.Fprintf(&b, "    fix     : %s\n", f.Fix)
			}
		}
		return b.String(), nil
	}
	return "", fmt.Errorf("unknown format %q (txt|md|json|csv|sarif)", format)
}

func writeOut(content, path string) error {
	if path == "" || path == "-" {
		fmt.Print(content)
		return nil
	}
	return os.WriteFile(path, []byte(content), 0o644)
}

// ====================================================================
//  REFERENCE
// ====================================================================

var refTopics = []string{"flags", "formats", "algs", "ctap", "extensions", "getinfo", "aaguids", "flow"}

func printRef(topic string) error {
	switch topic {
	case "flags":
		table([]string{"BIT", "FLAG", "MEANING"}, [][]string{
			{"0x01", "UP", "User Present (touch / presence test)"}, {"0x02", "RFU1", "reserved"},
			{"0x04", "UV", "User Verified (PIN / biometric)"}, {"0x08", "BE", "Backup Eligible (multi-device passkey)"},
			{"0x10", "BS", "Backup State (currently synced)"}, {"0x20", "RFU2", "reserved"},
			{"0x40", "AT", "Attested credential data present (registration)"}, {"0x80", "ED", "Extension data present"}})
	case "formats":
		table([]string{"FMT", "OFIDO VERIFIES", "TYPICAL"}, [][]string{
			{"none", "nothing to verify", "most passkeys"}, {"packed", "sig (self or x5c), cert profile, AAGUID ext, chain", "security keys"},
			{"fido-u2f", "U2F sig over 0x00‖rpIdHash‖cdh‖credId‖key, chain", "legacy U2F keys"},
			{"apple", "nonce extension = SHA-256(authData‖cdh), key match", "Apple devices"},
			{"android-key", "sig, key match, attestationChallenge, security level", "Android"},
			{"tpm", "certInfo magic/type/extraData/name, pubArea key, AIK sig", "Windows Hello"},
			{"android-safetynet", "reported as deprecated", "old Android"}})
	case "algs":
		ids := []int64{-7, -8, -35, -36, -257, -258, -259, -37, -38, -39, -47, -65535}
		var rows [][]string
		for _, id := range ids {
			a := coseAlgDB[id]
			rows = append(rows, []string{strconv.FormatInt(id, 10), a.Name, a.KeyType, a.Status, a.Description})
		}
		table([]string{"ALG", "NAME", "KTY", "STATUS", "DESCRIPTION"}, rows)
	case "ctap":
		var rows [][]string
		var ks []int
		for k := range ctapCommands {
			ks = append(ks, int(k))
		}
		sort.Ints(ks)
		for _, k := range ks {
			rows = append(rows, []string{fmt.Sprintf("0x%02x", k), ctapCommands[byte(k)]})
		}
		table([]string{"CMD", "CTAP2 COMMAND"}, rows)
		fmt.Println()
		rows, ks = nil, nil
		for k := range ctapErrorCodes {
			ks = append(ks, int(k))
		}
		sort.Ints(ks)
		for _, k := range ks {
			rows = append(rows, []string{fmt.Sprintf("0x%02x", k), ctapErrorCodes[byte(k)]})
		}
		table([]string{"CODE", "CTAP STATUS"}, rows)
	case "extensions", "getinfo":
		m := webauthnExtensions
		h := "EXTENSION"
		if topic == "getinfo" {
			m, h = getInfoOptions, "GETINFO OPTION"
		}
		var ks []string
		for k := range m {
			ks = append(ks, k)
		}
		sort.Strings(ks)
		var rows [][]string
		for _, k := range ks {
			rows = append(rows, []string{k, m[k]})
		}
		table([]string{h, "MEANING"}, rows)
	case "aaguids":
		var ks []string
		for k := range builtinAAGUIDs {
			ks = append(ks, k)
		}
		sort.Slice(ks, func(i, j int) bool { return builtinAAGUIDs[ks[i]].Name < builtinAAGUIDs[ks[j]].Name })
		var rows [][]string
		for _, k := range ks {
			b, _ := hex.DecodeString(k)
			rows = append(rows, []string{canonAAGUID(b), builtinAAGUIDs[k].Name, builtinAAGUIDs[k].Kind})
		}
		table([]string{"AAGUID", "AUTHENTICATOR", "KIND"}, rows)
		info(fmt.Sprintf("built-in subset; %d more from the MDS blob loaded with --mds", len(mdsDB)))
	case "flow":
		for _, s := range []string{
			"Registration: server sends a random challenge → authenticator creates a key pair →",
			"  browser returns attestationObject + clientDataJSON. The RP checks type, challenge, origin,",
			"  rpIdHash, UP/UV, the attestation statement, then stores credentialId, COSE key and signCount.",
			"Login: server sends a fresh challenge → authenticator signs authenticatorData ‖ SHA-256(clientDataJSON).",
			"  The RP checks type, challenge, origin, rpIdHash, UP/UV, the signature with the stored key,",
			"  and that signCount grew (or is 0) — a counter that goes backwards indicates a cloned key.",
		} {
			info(s)
		}
	default:
		return fmt.Errorf("unknown topic %q (%s)", topic, strings.Join(refTopics, "|"))
	}
	return nil
}

// ====================================================================
//  TEST VECTORS (real keys, real signatures) — demo + self-test
// ====================================================================

func coseOf(pub crypto.PublicKey, alg int64) []byte {
	switch k := pub.(type) {
	case *ecdsa.PublicKey:
		size := (k.Curve.Params().BitSize + 7) / 8
		crv := map[int]int64{256: 1, 384: 2, 521: 3}[k.Curve.Params().BitSize]
		return encodeCBOR(cMap(cInt(1), cInt(2), cInt(3), cInt(alg), cInt(-1), cInt(crv),
			cInt(-2), cBytes(k.X.FillBytes(make([]byte, size))), cInt(-3), cBytes(k.Y.FillBytes(make([]byte, size)))))
	case ed25519.PublicKey:
		return encodeCBOR(cMap(cInt(1), cInt(1), cInt(3), cInt(-8), cInt(-1), cInt(6), cInt(-2), cBytes(k)))
	case *rsa.PublicKey:
		return encodeCBOR(cMap(cInt(1), cInt(3), cInt(3), cInt(alg), cInt(-1), cBytes(k.N.Bytes()), cInt(-2), cBytes(big.NewInt(int64(k.E)).Bytes())))
	}
	return nil
}

func sign(priv crypto.Signer, alg int64, msg []byte) []byte {
	a := coseAlgDB[alg]
	if _, ok := priv.(ed25519.PrivateKey); ok {
		s, _ := priv.Sign(rand.Reader, msg, crypto.Hash(0))
		return s
	}
	h := a.Hash.New()
	h.Write(msg)
	d := h.Sum(nil)
	if strings.HasPrefix(a.Name, "PS") {
		s, _ := priv.Sign(rand.Reader, d, &rsa.PSSOptions{SaltLength: rsa.PSSSaltLengthEqualsHash, Hash: a.Hash})
		return s
	}
	s, _ := priv.Sign(rand.Reader, d, a.Hash)
	return s
}

func authDataOf(rpID string, flags byte, count uint32, aaguid, credID, cose []byte) []byte {
	h := sha256.Sum256([]byte(rpID))
	b := append([]byte(nil), h[:]...)
	b = append(b, flags)
	b = binary.BigEndian.AppendUint32(b, count)
	if cose != nil {
		b = append(b, aaguid...)
		b = binary.BigEndian.AppendUint16(b, uint16(len(credID)))
		b = append(b, credID...)
		b = append(b, cose...)
	}
	return b
}

func clientDataOf(typ, origin string, challenge []byte) []byte {
	return []byte(fmt.Sprintf(`{"type":%q,"challenge":%q,"origin":%q,"crossOrigin":false}`,
		typ, base64.RawURLEncoding.EncodeToString(challenge), origin))
}

func attObjOf(fmtName string, ad []byte, stmt cborValue) []byte {
	return encodeCBOR(cMap(cText("fmt"), cText(fmtName), cText("attStmt"), stmt, cText("authData"), cBytes(ad)))
}

type certSpec struct {
	cn, ou string
	isCA   bool
	exts   []pkix.Extension
	ekus   []asn1.ObjectIdentifier
}

func makeCert(s certSpec, pub crypto.PublicKey, parent *x509.Certificate, parentKey crypto.Signer) *x509.Certificate {
	serial, _ := rand.Int(rand.Reader, big.NewInt(1<<62))
	t := &x509.Certificate{SerialNumber: serial, Subject: pkix.Name{CommonName: s.cn, Organization: []string{"OWL Test"}},
		NotBefore: time.Now().Add(-time.Hour), NotAfter: time.Now().Add(24 * time.Hour), BasicConstraintsValid: true,
		IsCA: s.isCA, ExtraExtensions: s.exts, UnknownExtKeyUsage: s.ekus}
	if s.ou != "" {
		t.Subject.OrganizationalUnit = []string{s.ou}
	}
	if s.isCA {
		t.KeyUsage = x509.KeyUsageCertSign
	}
	if parent == nil {
		parent = t
	}
	der, err := x509.CreateCertificate(rand.Reader, t, parent, pub, parentKey)
	if err != nil {
		panic(err)
	}
	c, _ := x509.ParseCertificate(der)
	return c
}

func x5cOf(cs ...*x509.Certificate) cborValue {
	v := cborValue{Type: cborArray}
	for _, c := range cs {
		v.Items = append(v.Items, cBytes(c.Raw))
	}
	return v
}

func responseJSON(credID, clientData, attObj, authData, sig []byte) []byte {
	e := base64.RawURLEncoding.EncodeToString
	resp := map[string]any{"clientDataJSON": e(clientData)}
	if attObj != nil {
		resp["attestationObject"] = e(attObj)
	} else {
		resp["authenticatorData"], resp["signature"] = e(authData), e(sig)
	}
	b, _ := json.Marshal(map[string]any{"id": e(credID), "rawId": e(credID), "type": "public-key", "response": resp})
	return b
}

func runDemo() []*Report {
	key, _ := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	credID := make([]byte, 32)
	rand.Read(credID)
	aaguid, _ := hex.DecodeString("fbfc3007154e4ecc8c0b6e020557d7bd")
	chal := make([]byte, 32)
	rand.Read(chal)
	origin := "https://login.owlsec.org"
	// registration: packed self-attestation, synced passkey (BE|BS), UV
	cd := clientDataOf("webauthn.create", origin, chal)
	cdh := sha256.Sum256(cd)
	ad := authDataOf("owlsec.org", 0x01|0x04|0x08|0x10|0x40, 0, aaguid, credID, coseOf(&key.PublicKey, -7))
	att := attObjOf("packed", ad, cMap(cText("alg"), cInt(-7), cText("sig"), cBytes(sign(key, -7, append(append([]byte(nil), ad...), cdh[:]...)))))
	o := checkOpts{origin: origin, challenge: chal}
	reg := auditRegistration("demo registration (packed self-attestation)", att, cd, o)
	o.credKey, _ = parseCOSEKey(coseOf(&key.PublicKey, -7))
	// good login
	chal2 := make([]byte, 32)
	rand.Read(chal2)
	cd2 := clientDataOf("webauthn.get", origin, chal2)
	h2 := sha256.Sum256(cd2)
	ad2 := authDataOf("owlsec.org", 0x01|0x04|0x08|0x10, 0, nil, nil, nil)
	o.challenge = chal2
	good := auditAuthentication("demo login (valid)", ad2, cd2, sign(key, -7, append(append([]byte(nil), ad2...), h2[:]...)), o)
	// phished login: look-alike origin, replayed challenge, counter went back
	cd3 := clientDataOf("webauthn.get", "https://login-owlsec.org.evil.example", chal)
	h3 := sha256.Sum256(cd3)
	ad3 := authDataOf("owlsec.org", 0x01, 5, nil, nil, nil)
	o.prevCount = 9
	bad := auditAuthentication("demo login (phishing proxy + replay + clone)", ad3, cd3, sign(key, -7, append(append([]byte(nil), ad3...), h3[:]...)), o)
	return []*Report{reg, good, bad}
}

func runSelfTest() int {
	var rows [][]string
	fail, total := 0, 0
	check := func(name, expect, got string, ok bool) {
		total++
		res := col("PASS", GRN+B)
		if !ok {
			res = col("FAIL", R+B)
			fail++
		}
		rows = append(rows, []string{trunc(name, 38), trunc(expect, 24), trunc(got, 30), res})
	}
	has := func(r *Report, id string) bool {
		for _, f := range r.Findings {
			if f.ID == id {
				return true
			}
		}
		return false
	}
	worst := func(r *Report) string {
		w := "none"
		for _, f := range r.Findings {
			if sevRank[f.Severity] > sevRank[w] {
				w = f.Severity
			}
		}
		return w
	}
	ids := func(r *Report) string {
		var s []string
		for _, f := range r.Findings {
			if sevRank[f.Severity] >= sevRank[SevMedium] {
				s = append(s, f.ID)
			}
		}
		return strings.Join(s, ",")
	}
	clean := func(r *Report) bool { return sevRank[worst(r)] < sevRank[SevMedium] }

	origin, rp := "https://app.owlsec.org", "owlsec.org"
	chal := bytes.Repeat([]byte{0x5a, 0x13, 0xc7, 0x99}, 8)
	for i := range chal {
		chal[i] ^= byte(i * 37)
	}
	o := checkOpts{origin: origin, rpID: rp, challenge: chal}
	credID := bytes.Repeat([]byte{0xC1}, 32)
	aaguid, _ := hex.DecodeString("2fc0579f811347eab116bb5a8db9202a")
	ecKey, _ := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	cdC := clientDataOf("webauthn.create", origin, chal)
	cdh := sha256.Sum256(cdC)
	signedBy := func(ad []byte) []byte { return append(append([]byte(nil), ad...), cdh[:]...) }

	// packed self attestation
	ad := authDataOf(rp, 0x45, 0, aaguid, credID, coseOf(&ecKey.PublicKey, -7))
	att := attObjOf("packed", ad, cMap(cText("alg"), cInt(-7), cText("sig"), cBytes(sign(ecKey, -7, signedBy(ad)))))
	r := auditRegistration("t", att, cdC, o)
	check("packed self-attestation ES256 valid", "no MEDIUM+", ids(r), clean(r))
	bad := append([]byte(nil), ad...)
	bad[36] ^= 1 // signCount byte
	r = auditRegistration("t", attObjOf("packed", bad, cMap(cText("alg"), cInt(-7), cText("sig"), cBytes(sign(ecKey, -7, signedBy(ad))))), cdC, o)
	check("tampered authData → signature invalid", "OFIDO-ATT-013", ids(r), has(r, "OFIDO-ATT-013"))

	// packed full attestation with CA, AAGUID extension, --roots
	caKey, _ := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	ca := makeCert(certSpec{cn: "OWL Attestation Root", isCA: true}, &caKey.PublicKey, nil, caKey)
	attKey, _ := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	aext, _ := asn1.Marshal(aaguid)
	leaf := makeCert(certSpec{cn: "OWL Key Batch 7", ou: "Authenticator Attestation", exts: []pkix.Extension{{Id: oidFIDOAAGUID, Value: aext}}},
		&attKey.PublicKey, ca, caKey)
	stmt := cMap(cText("alg"), cInt(-7), cText("sig"), cBytes(sign(attKey, -7, signedBy(ad))), cText("x5c"), x5cOf(leaf))
	o.roots = []*x509.Certificate{ca}
	r = auditRegistration("t", attObjOf("packed", ad, stmt), cdC, o)
	check("packed x5c → trusted root", "no MEDIUM+", ids(r), clean(r) && strings.Contains(fmt.Sprint(r.Stats), "trusted root"))
	other, _ := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	o.roots = []*x509.Certificate{makeCert(certSpec{cn: "Other Root", isCA: true}, &other.PublicKey, nil, other)}
	r = auditRegistration("t", attObjOf("packed", ad, stmt), cdC, o)
	check("packed x5c → untrusted root", "OFIDO-X509-005", ids(r), has(r, "OFIDO-X509-005"))
	o.roots = nil
	ad2 := authDataOf(rp, 0x45, 0, make([]byte, 16), credID, coseOf(&ecKey.PublicKey, -7))
	stmt2 := cMap(cText("alg"), cInt(-7), cText("sig"), cBytes(sign(attKey, -7, signedBy(ad2))), cText("x5c"), x5cOf(leaf))
	r = auditRegistration("t", attObjOf("packed", ad2, stmt2), cdC, o)
	check("cert AAGUID ≠ authData AAGUID", "OFIDO-ATT-017", ids(r), has(r, "OFIDO-ATT-017"))

	// fido-u2f
	zero := make([]byte, 16)
	adU := authDataOf(rp, 0x41, 0, zero, credID, coseOf(&ecKey.PublicKey, -7))
	msg := append([]byte{0}, adU[:32]...)
	msg = append(append(append(msg, cdh[:]...), credID...), 0x04)
	msg = append(append(msg, ecKey.X.FillBytes(make([]byte, 32))...), ecKey.Y.FillBytes(make([]byte, 32))...)
	r = auditRegistration("t", attObjOf("fido-u2f", adU, cMap(cText("sig"), cBytes(sign(attKey, -7, msg)), cText("x5c"), x5cOf(leaf))), cdC, o)
	check("fido-u2f signature valid", "fact ✔", ids(r), strings.Contains(fmt.Sprint(r.Stats), "fido-u2f signature valid"))

	// apple: nonce extension = SHA-256(authData‖cdh), cert key = credential key
	nonce := sha256.Sum256(signedBy(ad))
	nv, _ := asn1.Marshal(struct {
		Nonce []byte `asn1:"tag:1,explicit"`
	}{nonce[:]})
	apple := makeCert(certSpec{cn: "apple-leaf", exts: []pkix.Extension{{Id: oidAppleNonce, Value: nv}}}, &ecKey.PublicKey, ca, caKey)
	r = auditRegistration("t", attObjOf("apple", ad, cMap(cText("x5c"), x5cOf(apple, ca))), cdC, o)
	check("apple nonce + key match", "fact ✔", ids(r), strings.Contains(fmt.Sprint(r.Stats), "apple anonymous attestation"))
	r = auditRegistration("t", attObjOf("apple", ad2, cMap(cText("x5c"), x5cOf(apple, ca))), cdC, o)
	check("apple nonce for other authData", "OFIDO-ATT-031", ids(r), has(r, "OFIDO-ATT-031"))

	// android-key (TEE)
	kd, _ := asn1.Marshal(struct {
		AttVersion  int
		AttSecLevel asn1.Enumerated
		KMVersion   int
		KMSecLevel  asn1.Enumerated
		Challenge   []byte
		UniqueID    []byte
		SoftwareEnf asn1.RawValue
		TeeEnforced asn1.RawValue
	}{3, 1, 4, 1, cdh[:], []byte{}, asn1.RawValue{FullBytes: []byte{0x30, 0}}, asn1.RawValue{FullBytes: []byte{0x30, 0}}})
	andCert := makeCert(certSpec{cn: "android-leaf", exts: []pkix.Extension{{Id: oidAndroidKey, Value: kd}}}, &ecKey.PublicKey, ca, caKey)
	r = auditRegistration("t", attObjOf("android-key", ad, cMap(cText("alg"), cInt(-7), cText("sig"), cBytes(sign(ecKey, -7, signedBy(ad))), cText("x5c"), x5cOf(andCert, ca))), cdC, o)
	check("android-key TEE: sig, key, challenge", "fact ✔", ids(r), strings.Contains(fmt.Sprint(r.Stats), "android-key signature, key and challenge valid") && clean(r))

	// tpm (ECC P-256 credential, AIK P-256)
	pubArea := binary.BigEndian.AppendUint16(nil, 0x0023)
	pubArea = binary.BigEndian.AppendUint16(pubArea, 0x000B)
	pubArea = binary.BigEndian.AppendUint32(pubArea, 0x00060472)
	pubArea = binary.BigEndian.AppendUint16(pubArea, 0)
	pubArea = append(pubArea, 0x00, 0x10, 0x00, 0x10, 0x00, 0x03, 0x00, 0x10)
	pubArea = append(binary.BigEndian.AppendUint16(pubArea, 32), ecKey.X.FillBytes(make([]byte, 32))...)
	pubArea = append(binary.BigEndian.AppendUint16(pubArea, 32), ecKey.Y.FillBytes(make([]byte, 32))...)
	extra := sha256.Sum256(signedBy(ad))
	pubHash := sha256.Sum256(pubArea)
	certInfo := binary.BigEndian.AppendUint32(nil, 0xff544347)
	certInfo = binary.BigEndian.AppendUint16(certInfo, 0x8017)
	certInfo = binary.BigEndian.AppendUint16(certInfo, 0)
	certInfo = append(binary.BigEndian.AppendUint16(certInfo, 32), extra[:]...)
	certInfo = append(certInfo, make([]byte, 17+8)...)
	certInfo = append(binary.BigEndian.AppendUint16(certInfo, 34), append([]byte{0x00, 0x0B}, pubHash[:]...)...)
	certInfo = binary.BigEndian.AppendUint16(certInfo, 0)
	aik := makeCert(certSpec{cn: "", ekus: []asn1.ObjectIdentifier{oidTCGKpAIKCert}}, &attKey.PublicKey, ca, caKey)
	tpmStmt := func(ci []byte) cborValue {
		return cMap(cText("ver"), cText("2.0"), cText("alg"), cInt(-7), cText("x5c"), x5cOf(aik, ca), cText("sig"), cBytes(sign(attKey, -7, ci)),
			cText("certInfo"), cBytes(ci), cText("pubArea"), cBytes(pubArea))
	}
	r = auditRegistration("t", attObjOf("tpm", ad, tpmStmt(certInfo)), cdC, o)
	check("tpm certInfo + pubArea + AIK sig", "fact ✔", ids(r), strings.Contains(fmt.Sprint(r.Stats), "tpm certInfo") && clean(r))
	ci2 := append([]byte(nil), certInfo...)
	ci2[12] ^= 0xFF // inside extraData
	r = auditRegistration("t", attObjOf("tpm", ad, tpmStmt(ci2)), cdC, o)
	check("tpm extraData for other ceremony", "OFIDO-TPM-007", ids(r), has(r, "OFIDO-TPM-007"))

	// assertions with every algorithm family
	edPub, edPriv, _ := ed25519.GenerateKey(rand.Reader)
	rsaKey, _ := rsa.GenerateKey(rand.Reader, 2048)
	cdG := clientDataOf("webauthn.get", origin, chal)
	hG := sha256.Sum256(cdG)
	adG := authDataOf(rp, 0x05, 10, nil, nil, nil)
	msgG := append(append([]byte(nil), adG...), hG[:]...)
	okAll, badAll := true, true
	for _, x := range []struct {
		priv crypto.Signer
		pub  crypto.PublicKey
		alg  int64
	}{{ecKey, &ecKey.PublicKey, -7}, {edPriv, edPub, -8}, {rsaKey, &rsaKey.PublicKey, -257}, {rsaKey, &rsaKey.PublicKey, -37}} {
		o.credKey, _ = parseCOSEKey(coseOf(x.pub, x.alg))
		s := sign(x.priv, x.alg, msgG)
		if r := auditAuthentication("t", adG, cdG, s, o); !clean(r) || !strings.Contains(fmt.Sprint(r.Stats), "signature valid") {
			okAll = false
		}
		s[len(s)/2] ^= 1
		if r := auditAuthentication("t", adG, cdG, s, o); !has(r, "OFIDO-SIG-001") {
			badAll = false
		}
	}
	check("assertion ES256 / EdDSA / RS256 / PS256", "valid · tamper caught", fmt.Sprint(okAll, badAll), okAll && badAll)

	// relying-party checks
	o.credKey, _ = parseCOSEKey(coseOf(&ecKey.PublicKey, -7))
	phish := clientDataOf("webauthn.get", "https://app.owlsec.org.evil.example", chal)
	r = auditAuthentication("t", adG, phish, nil, o)
	check("phishing origin", "OFIDO-CD-002", ids(r), has(r, "OFIDO-CD-002") && worst(r) == SevCritical)
	o2 := o
	o2.challenge = []byte("a-different-challenge-0123456789")
	r = auditAuthentication("t", adG, cdG, nil, o2)
	check("replayed challenge", "OFIDO-CD-005", ids(r), has(r, "OFIDO-CD-005") && worst(r) == SevCritical)
	r = auditAuthentication("t", adG, cdC, nil, o)
	check("create clientData used for login", "OFIDO-CD-001", ids(r), has(r, "OFIDO-CD-001"))
	o3 := o
	o3.rpID = ""
	r = auditAuthentication("t", adG, cdG, nil, o3)
	check("rpId derived: parent of app.owlsec.org", "owlsec.org ✔", fmt.Sprint(r.Stats), clean(r) && strings.Contains(fmt.Sprint(r.Stats), "owlsec.org ✔ (derived"))
	r = auditAuthentication("t", authDataOf("evil.example", 0x05, 10, nil, nil, nil), cdG, nil, o3)
	check("rpIdHash for another site", "OFIDO-RPID-001", ids(r), has(r, "OFIDO-RPID-001"))
	o4 := o
	o4.prevCount = 10
	r = auditAuthentication("t", adG, cdG, nil, o4)
	check("signCount did not increase (clone)", "OFIDO-AD-010", ids(r), has(r, "OFIDO-AD-010"))
	r = auditAuthentication("t", authDataOf(rp, 0x15, 0, nil, nil, nil), cdG, nil, o)
	check("BS without BE flag", "OFIDO-AD-003", ids(r), has(r, "OFIDO-AD-003"))
	o5 := o
	o5.deviceBound = true
	r = auditAuthentication("t", authDataOf(rp, 0x1D, 0, nil, nil, nil), cdG, nil, o5)
	check("synced passkey vs device-bound policy", "OFIDO-AD-005", ids(r), has(r, "OFIDO-AD-005"))

	// JSON response round trip (registration + authentication)
	regJSON := responseJSON(credID, cdC, att, nil, nil)
	c, err := parseResponseJSON(regJSON)
	check("PublicKeyCredential JSON (registration)", "registration", fmt.Sprint(c != nil && c.kind == "registration", err),
		err == nil && c.kind == "registration" && bytes.Equal(c.attObj, att))
	c, err = parseResponseJSON(responseJSON(credID, cdG, nil, adG, []byte{1, 2, 3}))
	check("PublicKeyCredential JSON (login)", "authentication", fmt.Sprint(err), err == nil && c.kind == "authentication")

	// MDS: status report makes the model untrusted
	mds := fmt.Sprintf(`{"no":42,"nextUpdate":"2026-12-01","entries":[{"aaguid":"%s","metadataStatement":{"description":"Test Key","attestationRootCertificates":[]},"statusReports":[{"status":"FIDO_CERTIFIED_L1","effectiveDate":"2024-01-01"},{"status":"ATTESTATION_KEY_COMPROMISE","effectiveDate":"2026-05-01"}]}]}`, canonAAGUID(aaguid))
	tmp, _ := os.CreateTemp("", "ofido-mds-*.json")
	tmp.WriteString(mds)
	tmp.Close()
	defer os.Remove(tmp.Name())
	n, err := loadMDS(tmp.Name())
	o.roots = nil
	r = auditRegistration("t", att, cdC, o)
	check("MDS status ATTESTATION_KEY_COMPROMISE", "OFIDO-MDS-001", fmt.Sprint(n, err, ids(r)), n == 1 && has(r, "OFIDO-MDS-001"))
	delete(mdsDB, hex.EncodeToString(aaguid))

	// hostile CBOR: lying lengths, deep nesting, indefinite items, fuzz
	hostile := map[string][]byte{
		"array claims 2^32 items": {0x9a, 0xff, 0xff, 0xff, 0xff, 0x00},
		"map claims 2^63 pairs":   {0xbb, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff},
		"1000-deep nesting":       append(bytes.Repeat([]byte{0x81}, 1000), 0x00),
		"indefinite array":        {0x9f, 0x01, 0xff},
		"bytes past the end":      {0x5a, 0x00, 0x10, 0x00, 0x00, 0x01},
	}
	rejected := 0
	for _, h := range hostile {
		if _, err := decodeCBOR(h); err != nil {
			rejected++
		}
	}
	check("hostile CBOR rejected safely", "5/5", fmt.Sprintf("%d/5", rejected), rejected == 5)
	rng := mrand.New(mrand.NewSource(11))
	panics := 0
	for i := 0; i < 1500; i++ {
		src := [][]byte{att, attObjOf("tpm", ad, tpmStmt(certInfo)), attObjOf("packed", ad, stmt)}[i%3]
		m := append([]byte(nil), src...)
		for k := 0; k < 1+rng.Intn(6); k++ {
			m[rng.Intn(len(m))] = byte(rng.Intn(256))
		}
		if rng.Intn(5) == 0 {
			m = m[:rng.Intn(len(m))+1]
		}
		func() {
			defer func() {
				if recover() != nil {
					panics++
				}
			}()
			auditRegistration("fuzz", m, cdC, o)
		}()
	}
	check("1500 mutated attestations: no panic", "0", strconv.Itoa(panics), panics == 0)
	selfTestExtras(check)

	table([]string{"CASE", "EXPECT", "GOT", "RESULT"}, rows)
	fmt.Println()
	if fail == 0 {
		okMsg(fmt.Sprintf("self-test: %d/%d passed", total, total))
	} else {
		errMsg(fmt.Sprintf("self-test: %d/%d FAILED", fail, total))
	}
	return fail
}

// selfTestExtras covers options, credential store, getInfo and the
// test-vector generator (each generated case must get its expected verdict).
func selfTestExtras(check func(name, expect, got string, ok bool)) {
	ids := func(r *Report) map[string]bool {
		m := map[string]bool{}
		for _, f := range r.Findings {
			m[f.ID] = true
		}
		return m
	}
	b64 := base64.RawURLEncoding.EncodeToString
	good := fmt.Sprintf(`{"publicKey":{"challenge":%q,"rp":{"id":"example.com","name":"Example"},"user":{"id":%q,"name":"jane","displayName":"Jane"},
"pubKeyCredParams":[{"type":"public-key","alg":-7},{"type":"public-key","alg":-8},{"type":"public-key","alg":-257}],
"authenticatorSelection":{"residentKey":"required","userVerification":"required"},"excludeCredentials":[{"type":"public-key","id":"AAAA"}],
"timeout":300000,"attestation":"none","extensions":{"credProps":true}}}`, b64([]byte("\x9a\x13\xf0\x44\x8c\x21\x7e\xb2\x55\xd9\x03\x6a\xe1\x47\xbc\x18\x92\x3f\xa7\x0e\x5b\xc4\x71\x2d\x88\xf6\x19\xae\x30\x64\xdb\x05")), b64([]byte("\x01\x7f\x33\xc2\x9e\x45\xab\x10\x6d\xe8\x22\x91\x5c\xf7\x08\xb4")))
	r := auditOptions("t", []byte(good), checkOpts{origin: "https://login.example.com"})
	worstSev := func(r *Report) string {
		w := "none"
		for _, f := range r.Findings {
			if sevRank[f.Severity] > sevRank[w] {
				w = f.Severity
			}
		}
		return w
	}
	check("RP options: good creation options", "nothing above LOW", worstSev(r), sevRank[worstSev(r)] <= sevRank[SevLow])
	bad := `{"challenge":"MTIzNA","rp":{"id":"evil.example"},"user":{"id":"` + b64([]byte("jane@example.com")) + `","name":"jane@example.com"},
"pubKeyCredParams":[{"type":"public-key","alg":-65535}],"authenticatorSelection":{"residentKey":"required","userVerification":"discouraged"},"timeout":3600000}`
	r = auditOptions("t", []byte(bad), checkOpts{origin: "https://example.com"})
	m := ids(r)
	check("RP options: PII handle, RS1, short challenge, rpId", "5 findings", fmt.Sprint(len(r.Findings)),
		m["OFIDO-OPT-002"] && m["OFIDO-OPT-012"] && m["OFIDO-OPT-022"] && m["OFIDO-OPT-032"] && m["OFIDO-OPT-033"] && m["OFIDO-OPT-042"] && m["OFIDO-OPT-061"])

	// credential store: shared key, duplicate id, single-key user, weak RS1
	k1, _ := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	k2, _ := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	rk, _ := rsa.GenerateKey(rand.Reader, 2048)
	c1, c2, c3 := b64(coseOf(&k1.PublicKey, -7)), b64(coseOf(&k2.PublicKey, -7)), b64(coseOf(&rk.PublicKey, -65535))
	csv := "user,credential_id,public_key,sign_count,backup_eligible,last_used\n" +
		"alice," + b64(bytes.Repeat([]byte{1}, 32)) + "," + c1 + ",4,false,2026-10-01\n" +
		"bob," + b64(bytes.Repeat([]byte{2}, 32)) + "," + c1 + ",9,true,2026-10-01\n" +
		"bob," + b64(bytes.Repeat([]byte{2}, 32)) + "," + c2 + ",1,true,2026-10-01\n" +
		"carol," + b64(bytes.Repeat([]byte{3}, 32)) + "," + c3 + ",0,false,2023-01-01\n"
	tmp, _ := os.CreateTemp("", "ofido-store-*.csv")
	tmp.WriteString(csv)
	tmp.Close()
	defer os.Remove(tmp.Name())
	cs, err := loadCredStore(tmp.Name())
	r = auditCredStore("t", cs)
	m = ids(r)
	var got []string
	for _, f := range r.Findings {
		got = append(got, strings.TrimPrefix(f.ID, "OFIDO-STORE-"))
	}
	check("cred store: dup id, shared key, RS1, lone, stale", "001 002 004 007 008", fmt.Sprint(len(cs), err, got),
		err == nil && m["OFIDO-STORE-001"] && m["OFIDO-STORE-002"] && m["OFIDO-STORE-004"] && m["OFIDO-STORE-007"] && m["OFIDO-STORE-008"])

	// binary keys ending in whitespace-like bytes must survive loading
	trailing := 0
	for i := 0; i < 400 && trailing < 20; i++ {
		k, _ := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
		c := coseOf(&k.PublicKey, -7)
		if last := c[len(c)-1]; last == 0x20 || last == 0x0a || last == 0x0d || last == 0x09 {
			trailing++
			if ck, err := loadCredentialKey(b64(c)); err != nil || ck.Pub == nil || !sameKey(ck.Pub, &k.PublicKey) {
				trailing = -1000
			}
		}
	}
	check("keys ending in 0x20/0x0a load intact", "all", strconv.Itoa(trailing), trailing > 0)

	// getInfo
	r = auditGetInfo("t", demoGetInfo())
	m = ids(r)
	check("getInfo: PIN unset, UV not required, PIN length 4", "3 rules", fmt.Sprint(len(r.Findings)),
		m["OFIDO-INFO-011"] && m["OFIDO-INFO-012"] && m["OFIDO-INFO-020"] && strings.Contains(fmt.Sprint(r.Stats), "YubiKey"))

	// generator: every vector must get its expected verdict
	dir, _ := os.MkdirTemp("", "ofido-gen-")
	defer os.RemoveAll(dir)
	gm, err := genTests(dir, "https://shop.example.com", "example.com", nil)
	agree := 0
	var miss []string
	for _, c := range gm.Cases {
		if strings.HasPrefix(c.OFIDO, strings.TrimSuffix(c.Expect, "-if-uv-required")) {
			agree++
		} else {
			miss = append(miss, c.Name+"="+c.OFIDO)
		}
	}
	check("generated RP vectors judged as expected", fmt.Sprintf("%d/%d", len(gm.Cases), len(gm.Cases)), fmt.Sprintf("%d/%d %v %v", agree, len(gm.Cases), err, miss),
		err == nil && len(gm.Cases) >= 26 && agree == len(gm.Cases))
}

// ====================================================================
//  INTERACTIVE TUI
// ====================================================================

var lastReport *Report
var policy checkOpts

type tuiAction struct {
	name, desc string
	fn         func()
}

var tuiActions []tuiAction

func init() {
	tuiActions = []tuiAction{
		{"Verify a response JSON", "PublicKeyCredential from the browser", uiResponse},
		{"Verify a registration", "attestationObject + clientDataJSON", uiRegistration},
		{"Verify a login", "authenticatorData + signature + key", uiLogin},
		{"Policy", "origin · rpId · challenge · UV · roots", uiPolicy},
		{"Audit RP options", "creation / request options JSON", uiOptions},
		{"Audit credential store", "CSV / JSON of stored credentials", uiCredStore},
		{"Analyse getInfo", "what a security key can enforce", uiGetInfo},
		{"Generate RP test vectors", "signed good + malicious ceremonies", uiGenTests},
		{"Decode CBOR", "diagnostic notation", uiCBOR},
		{"Parse a COSE key", "kty · alg · curve · usability", uiCOSE},
		{"Look up an AAGUID", "built-in list or loaded MDS", uiAAGUID},
		{"Load FIDO MDS blob", "models, roots, status reports", uiMDS},
		{"Reference", "flags · formats · algs · CTAP · extensions", uiRef},
		{"Export last report", "txt · md · json · csv · sarif", uiExport},
		{"Run demo", "registration · good login · phished login", uiDemo},
		{"Self-test", "real keys, every format, fuzzing", func() { sectionHeader("Self-Test"); runSelfTest() }},
	}
}

func mainMenu() {
	for {
		clear()
		banner()
		fmt.Println("  " + col("⬡  Main Menu", B+CY) + col("     origin "+defaultStr(policy.origin, "(not set)"), DIM))
		fmt.Println()
		for i, a := range tuiActions {
			fmt.Println("  " + col(pad(fmt.Sprintf("[%d]", i+1), 4), CY+B) + "  " +
				col(pad(a.name, 26), W) + col("─ "+a.desc, DIM))
		}
		fmt.Println()
		fmt.Println("  " + col(pad("[H]", 4), YLW+B) + "  " + col(pad("Help & Usage", 26), W) + col("─ How to use, every option, CLI flags & examples", DIM))
		fmt.Println("  " + col(pad("[0]", 4), R+B) + "  " + col(pad("Exit", 26), W) + col("─ Quit "+APPNAME, DIM))
		fmt.Println()
		rule()
		c := strings.TrimLeft(prompt("Select option"), "0")
		if c == "" {
			clear()
			okMsg("Goodbye.")
			return
		}
		if strings.EqualFold(c, "h") || strings.EqualFold(c, "help") || c == "?" {
			tuiHelp()
			continue
		}
		n, err := strconv.Atoi(c)
		if err != nil || n < 1 || n > len(tuiActions) {
			errMsg("Unknown option")
			pause()
			continue
		}
		clear()
		banner()
		tuiActions[n-1].fn()
		pause()
	}
}

func show(r *Report) {
	lastReport = r
	printReport(r)
}

func auditCeremony(target string, c *ceremony, o checkOpts) *Report {
	if c.kind == "registration" {
		return auditRegistration(target, c.attObj, c.clientData, o)
	}
	r := auditAuthentication(target, c.authData, c.clientData, c.signature, o)
	if len(c.credID) > 0 {
		r.Stats = append([]KV{{"credentialId", base64.RawURLEncoding.EncodeToString(c.credID)}}, r.Stats...)
	}
	return r
}

func uiResponse() {
	sectionHeader("Verify a Response JSON")
	p := prompt("file with PublicKeyCredential JSON")
	data, err := os.ReadFile(p)
	if err != nil {
		errMsg(err.Error())
		return
	}
	c, err := parseResponseJSON(data)
	if err != nil {
		errMsg(err.Error())
		return
	}
	if c.kind == "authentication" && policy.credKey == nil {
		if k := prompt("stored credential key / registration JSON (blank = skip signature)"); k != "" {
			if ck, err := loadCredentialKey(k); err == nil {
				policy.credKey = ck
			} else {
				warnMsg(err.Error())
			}
		}
	}
	fmt.Println()
	show(auditCeremony(p, c, policy))
}

func uiRegistration() {
	sectionHeader("Verify a Registration")
	a := prompt("attestationObject (file / hex / base64)")
	att, err := loadBytes(a)
	if err != nil {
		errMsg(err.Error())
		return
	}
	var cd []byte
	if s := prompt("clientDataJSON (file / JSON / base64, blank = none)"); s != "" {
		cd = loadClientData(s)
	}
	fmt.Println()
	show(auditRegistration(a, att, cd, policy))
}

func loadClientData(s string) []byte {
	if strings.HasPrefix(strings.TrimSpace(s), "{") {
		return []byte(s)
	}
	if b, err := os.ReadFile(s); err == nil {
		if t := bytes.TrimSpace(b); len(t) > 0 && t[0] == '{' {
			return t
		}
		s = string(b)
	}
	b, _ := decodeB64(s)
	return b
}

func uiLogin() {
	sectionHeader("Verify a Login")
	a := prompt("authenticatorData (file / hex / base64)")
	ad, err := loadBytes(a)
	if err != nil {
		errMsg(err.Error())
		return
	}
	var cd, sig []byte
	if s := prompt("clientDataJSON (blank = none)"); s != "" {
		cd = loadClientData(s)
	}
	if s := prompt("signature (blank = none)"); s != "" {
		sig, _ = loadBytes(s)
	}
	if k := prompt("stored credential key / registration JSON (blank = keep policy key)"); k != "" {
		if ck, err := loadCredentialKey(k); err == nil {
			policy.credKey = ck
		} else {
			warnMsg(err.Error())
		}
	}
	if v := prompt("stored signCount (blank = 0)"); v != "" {
		n, _ := strconv.ParseUint(v, 10, 32)
		policy.prevCount = uint32(n)
	}
	fmt.Println()
	show(auditAuthentication(a, ad, cd, sig, policy))
}

func uiPolicy() {
	sectionHeader("Verification Policy")
	keep := func(label, cur string) string {
		v := prompt(fmt.Sprintf("%s (blank = %s, - = clear)", label, defaultStr(cur, "unset")))
		switch v {
		case "":
			return cur
		case "-":
			return ""
		}
		return v
	}
	policy.origin = keep("expected origin", policy.origin)
	policy.rpID = keep("RP ID", policy.rpID)
	if c := keep("expected challenge (base64url / hex)", ""); c != "" {
		if b, err := decodeText(c); err == nil {
			policy.challenge = b
		}
	}
	yes := func(q string, cur bool) bool {
		switch strings.ToLower(prompt(fmt.Sprintf("%s [y/n] (blank = %v)", q, cur))) {
		case "y", "yes":
			return true
		case "n", "no":
			return false
		}
		return cur
	}
	policy.requireUV = yes("require user verification", policy.requireUV)
	policy.deviceBound = yes("reject synced passkeys (device-bound only)", policy.deviceBound)
	if p := prompt("attestation trust roots PEM (blank = keep)"); p != "" {
		if rs, err := loadRoots(p); err == nil {
			policy.roots = rs
			okMsg(fmt.Sprintf("%d root(s) loaded", len(rs)))
		} else {
			errMsg(err.Error())
		}
	}
	okMsg("policy updated")
}

func uiOptions() {
	sectionHeader("Audit RP Options")
	data, err := os.ReadFile(prompt("options JSON file"))
	if err != nil {
		errMsg(err.Error())
		return
	}
	if policy.origin == "" {
		policy.origin = prompt("site origin, e.g. https://example.com (blank = skip rpId check)")
	}
	fmt.Println()
	show(auditOptions("options", data, policy))
}

func uiCredStore() {
	sectionHeader("Audit Credential Store")
	p := prompt("CSV / JSON export of stored credentials")
	cs, err := loadCredStore(p)
	if err != nil {
		errMsg(err.Error())
		return
	}
	fmt.Println()
	show(auditCredStore(p, cs))
}

func uiGetInfo() {
	sectionHeader("Analyse getInfo")
	in := prompt("getInfo response (file / hex / base64, blank = demo key)")
	var b []byte
	var err error
	if in == "" {
		b, in = demoGetInfo(), "demo security key"
	} else if b, err = loadBytes(in); err != nil {
		errMsg(err.Error())
		return
	}
	fmt.Println()
	show(auditGetInfo(in, b))
}

func uiGenTests() {
	sectionHeader("Generate RP Test Vectors")
	dir := prompt("output directory (blank = ofido-vectors)")
	if dir == "" {
		dir = "ofido-vectors"
	}
	org := defaultStr(policy.origin, prompt("your site's origin, e.g. https://example.com"))
	m, err := genTests(dir, org, policy.rpID, policy.challenge)
	if err != nil {
		errMsg(err.Error())
		return
	}
	fmt.Println()
	printGen(dir, m)
}

func uiCBOR() {
	sectionHeader("Decode CBOR")
	b, err := loadBytes(prompt("CBOR (file / hex / base64)"))
	if err != nil {
		errMsg(err.Error())
		return
	}
	v, err := decodeCBOR(b)
	if err != nil {
		errMsg(err.Error())
		return
	}
	fmt.Println(v.pretty(1))
}

func uiCOSE() {
	sectionHeader("Parse a COSE Key")
	ck, err := loadCredentialKey(prompt("COSE / PEM key, attestation object or registration JSON"))
	if err != nil {
		errMsg(err.Error())
		return
	}
	for _, x := range ck.summarize() {
		kv(x.K, x.V)
	}
}

func uiAAGUID() {
	sectionHeader("Look Up an AAGUID")
	b, err := hex.DecodeString(strings.ReplaceAll(prompt("AAGUID"), "-", ""))
	if err != nil || len(b) != 16 {
		errMsg("an AAGUID is 16 bytes of hex (dashes optional)")
		return
	}
	if x, ok := lookupAAGUID(b); ok {
		kv("AAGUID", canonAAGUID(b))
		kv("Authenticator", x.Name)
		kv("Source", x.Source)
		if x.Status != "" {
			kv("MDS status", x.Status)
		}
		if len(x.Roots) > 0 {
			kv("Roots", fmt.Sprintf("%d attestation root(s)", len(x.Roots)))
		}
		return
	}
	warnMsg("not in the built-in list" + map[bool]string{true: " or the loaded MDS", false: " — load the MDS blob for full coverage"}[mdsLoaded != ""])
}

func uiMDS() {
	sectionHeader("Load FIDO MDS Blob")
	info("download the BLOB from https://mds3.fidoalliance.org/ (a JWT) — it is read offline")
	n, err := loadMDS(prompt("MDS file"))
	if err != nil {
		errMsg(err.Error())
		return
	}
	okMsg(fmt.Sprintf("%d authenticator models loaded — %s", n, mdsLoaded))
	warnMsg("the BLOB's JWT signature is not verified; obtain it over HTTPS from the FIDO Alliance")
}

func uiRef() {
	sectionHeader("Reference")
	t := prompt("topic [" + strings.Join(refTopics, "|") + "]")
	fmt.Println()
	if err := printRef(t); err != nil {
		errMsg(err.Error())
	}
}

func uiExport() {
	sectionHeader("Export Last Report")
	if lastReport == nil {
		warnMsg("verify something first")
		return
	}
	s, err := render(lastReport, prompt("format [txt|md|json|csv|sarif]"))
	if err != nil {
		errMsg(err.Error())
		return
	}
	out := prompt("output file (blank = stdout)")
	if err := writeOut(s, out); err != nil {
		errMsg(err.Error())
	} else if out != "" {
		okMsg("wrote " + out)
	}
}

func uiDemo() {
	for i, r := range runDemo() {
		if i > 0 {
			fmt.Println()
		}
		show(r)
	}
}

// ====================================================================
//  CLI
// ====================================================================

func usage() {
	banner()
	fmt.Print(`USAGE:
  OFIDO --response FILE [policy]                 browser PublicKeyCredential JSON
  OFIDO --attestation X [--clientdata Y]         registration (X/Y: file, hex or base64)
  OFIDO --authdata X --signature S --clientdata Y --credential KEY   login
  With no flags the interactive TUI starts.

POLICY:
  --origin URL          Expected origin (exact match)
  --rpid ID             Expected RP ID (default: origin host or a parent domain)
  --challenge B64       Challenge the server issued (base64url or hex)
  --prev-count N        Stored signCount (detects cloned authenticators)
  --credential KEY      Stored credential key: COSE, PEM/DER SPKI, attestation object or registration JSON
  --require-uv          Missing UV is HIGH instead of MEDIUM
  --device-bound        Reject synced (backup-eligible) passkeys
  --roots PEM           Trusted attestation roots for x5c chains
  --mds FILE            FIDO MDS3 BLOB (JWT or JSON): model names, roots, status reports

RELYING-PARTY AUDITS:
  --options FILE        Audit the creation / request options JSON your server sends
                        (challenge, rp.id vs --origin, user.id PII, algorithms, UV, timeout)
  --credstore FILE      Audit stored credentials (CSV or JSON array): duplicate IDs, shared
                        keys, weak algorithms, MDS-flagged models, single-key users, stale
  --getinfo X           Grade a CTAP2 authenticatorGetInfo response (CBOR file / hex / base64)
  --gen-tests DIR       Write signed good + malicious registration / login vectors for
                        your server (needs --origin; --rpid, --challenge optional)

TOOLS:
  --cbor X              Decode CBOR to diagnostic notation
  --cose X              Inspect a COSE / PEM key
  --aaguid HEX          Look up an authenticator model
  --ref TOPIC           flags | formats | algs | ctap | extensions | getinfo | aaguids | flow

OUTPUT:
  --format FMT          txt | md | json | csv | sarif   (default: coloured report)
  --output FILE         Write the report to FILE
  --demo                Registration, a valid login and a phished login (real signatures)
  --selftest            Every attestation format and algorithm with real keys, plus fuzzing
  --no-color, --version

EXIT CODES:
  0 accept · 1 error · 3 reject (HIGH or CRITICAL finding)

EXAMPLES:
  OFIDO --response reg.json --origin https://example.com --challenge Zm9vYmFy...
  OFIDO --response login.json --origin https://example.com --credential reg.json --prev-count 41
  OFIDO --attestation attobj.b64 --clientdata cdj.json --mds blob.jwt
  OFIDO --cbor a363666d74...
  OFIDO --options create-options.json --origin https://example.com
  OFIDO --credstore credentials.csv --mds blob.jwt
  OFIDO --gen-tests ./webauthn-vectors --origin https://example.com
`)
}

func main() { os.Exit(run()) }

func run() int {
	fs := flag.NewFlagSet(APPNAME, flag.ContinueOnError)
	fs.Usage = usage
	var (
		response    = fs.String("response", "", "")
		attestation = fs.String("attestation", "", "")
		authdata    = fs.String("authdata", "", "")
		clientdata  = fs.String("clientdata", "", "")
		signature   = fs.String("signature", "", "")
		credential  = fs.String("credential", "", "")
		origin      = fs.String("origin", "", "")
		rpid        = fs.String("rpid", "", "")
		challenge   = fs.String("challenge", "", "")
		prevCount   = fs.Uint("prev-count", 0, "")
		requireUV   = fs.Bool("require-uv", false, "")
		deviceBound = fs.Bool("device-bound", false, "")
		roots       = fs.String("roots", "", "")
		mds         = fs.String("mds", "", "")
		cborIn      = fs.String("cbor", "", "")
		coseIn      = fs.String("cose", "", "")
		aaguid      = fs.String("aaguid", "", "")
		ref         = fs.String("ref", "", "")
		format      = fs.String("format", "", "")
		output      = fs.String("output", "", "")
		demo        = fs.Bool("demo", false, "")
		self        = fs.Bool("selftest", false, "")
		nocol       = fs.Bool("no-color", false, "")
		ver         = fs.Bool("version", false, "")
		optionsIn   = fs.String("options", "", "")
		credstore   = fs.String("credstore", "", "")
		getinfo     = fs.String("getinfo", "", "")
		gentests    = fs.String("gen-tests", "", "")
	)
	if err := fs.Parse(os.Args[1:]); err != nil {
		if errors.Is(err, flag.ErrHelp) {
			return 0
		}
		return 1
	}
	if *nocol {
		noColor = true
	}
	fail := func(err error) int { errMsg(err.Error()); return 1 }
	if *mds != "" {
		n, err := loadMDS(*mds)
		if err != nil {
			return fail(err)
		}
		fmt.Fprintf(os.Stderr, "# MDS: %d models from %s\n", n, mdsLoaded)
	}
	o := checkOpts{origin: *origin, rpID: *rpid, prevCount: uint32(*prevCount), requireUV: *requireUV, deviceBound: *deviceBound}
	if *challenge != "" {
		b, err := decodeText(*challenge)
		if err != nil {
			return fail(fmt.Errorf("--challenge: %v", err))
		}
		o.challenge = b
	}
	if *roots != "" {
		rs, err := loadRoots(*roots)
		if err != nil {
			return fail(err)
		}
		o.roots = rs
	}
	if *credential != "" {
		ck, err := loadCredentialKey(*credential)
		if err != nil {
			return fail(fmt.Errorf("--credential: %v", err))
		}
		o.credKey = ck
	}
	var r *Report
	switch {
	case *ver:
		fmt.Printf("%s v%s — %s\n", APPNAME, VERSION, TAGLINE)
		return 0
	case *self:
		if runSelfTest() != 0 {
			return 1
		}
		return 0
	case *demo:
		banner()
		for i, x := range runDemo() {
			if i > 0 {
				fmt.Println()
			}
			printReport(x)
		}
		return 0
	case *ref != "":
		banner()
		if err := printRef(*ref); err != nil {
			return fail(err)
		}
		return 0
	case *cborIn != "":
		b, err := loadBytes(*cborIn)
		if err != nil {
			return fail(err)
		}
		v, err := decodeCBOR(b)
		if err != nil {
			return fail(err)
		}
		fmt.Println(v.pretty(0))
		return 0
	case *coseIn != "":
		ck, err := loadCredentialKey(*coseIn)
		if err != nil {
			return fail(err)
		}
		r = newReport(*coseIn, "cose")
		r.Stats = ck.summarize()
		if ck.Err != "" {
			r.add(SevHigh, "OFIDO-COSE-000", "cose", "Key is not usable", ck.Err, "")
		}
		r.finalize()
	case *gentests != "":
		if *origin == "" {
			return fail(errors.New("--gen-tests DIR needs --origin https://your.site (and optionally --rpid, --challenge)"))
		}
		m, err := genTests(*gentests, *origin, *rpid, o.challenge)
		if err != nil {
			return fail(err)
		}
		if *format == "json" {
			b, _ := json.MarshalIndent(m, "", "  ")
			writeOut(string(b)+"\n", *output)
		} else {
			banner()
			sectionHeader("Relying-Party Test Vectors")
			printGen(*gentests, m)
		}
		return 0
	case *optionsIn != "":
		data, err := os.ReadFile(*optionsIn)
		if err != nil {
			return fail(err)
		}
		r = auditOptions(*optionsIn, data, o)
	case *credstore != "":
		cs, err := loadCredStore(*credstore)
		if err != nil {
			return fail(err)
		}
		r = auditCredStore(*credstore, cs)
	case *getinfo != "":
		b, err := loadBytes(*getinfo)
		if err != nil {
			return fail(err)
		}
		r = auditGetInfo(*getinfo, b)
	case *aaguid != "":
		b, err := hex.DecodeString(strings.ReplaceAll(*aaguid, "-", ""))
		if err != nil || len(b) != 16 {
			return fail(errors.New("--aaguid needs 16 bytes of hex"))
		}
		r = newReport(canonAAGUID(b), "aaguid")
		if x, ok := lookupAAGUID(b); ok {
			r.fact("authenticator", x.Name)
			r.fact("source", x.Source)
			if x.Status != "" {
				r.fact("mds status", x.Status)
			}
			if badStatus[x.Status] {
				r.add(SevCritical, "OFIDO-MDS-001", "metadata", "Model has status "+x.Status, x.Name, "")
			}
		} else {
			r.add(SevInfo, "OFIDO-AAGUID-001", "metadata", "AAGUID unknown", canonAAGUID(b), "Load the MDS blob with --mds.")
		}
		r.finalize()
	case *response != "":
		data, err := os.ReadFile(*response)
		if err != nil {
			return fail(err)
		}
		c, err := parseResponseJSON(data)
		if err != nil {
			return fail(err)
		}
		r = auditCeremony(*response, c, o)
	case *attestation != "":
		b, err := loadBytes(*attestation)
		if err != nil {
			return fail(err)
		}
		var cd []byte
		if *clientdata != "" {
			cd = loadClientData(*clientdata)
		}
		r = auditRegistration(*attestation, b, cd, o)
	case *authdata != "":
		b, err := loadBytes(*authdata)
		if err != nil {
			return fail(err)
		}
		var cd, sig []byte
		if *clientdata != "" {
			cd = loadClientData(*clientdata)
		}
		if *signature != "" {
			if sig, err = loadBytes(*signature); err != nil {
				return fail(fmt.Errorf("--signature: %v", err))
			}
		}
		r = auditAuthentication(*authdata, b, cd, sig, o)
	case len(os.Args) == 1 || *mds != "":
		policy = o
		mainMenu()
		return 0
	default:
		usage()
		return 1
	}
	if *format == "" && *output == "" {
		banner()
		printReport(r)
	} else {
		s, err := render(r, *format)
		if err != nil {
			return fail(err)
		}
		if err := writeOut(s, *output); err != nil {
			return fail(err)
		}
	}
	if strings.HasPrefix(r.Verdict, "REJECT") {
		return 3
	}
	return 0
}

// ====================================================================
//  CTAP / EXTENSION REFERENCE TABLES
// ====================================================================

var ctapCommands = map[byte]string{
	0x01: "authenticatorMakeCredential",
	0x02: "authenticatorGetAssertion",
	0x03: "authenticatorGetNextAssertion",
	0x04: "authenticatorGetInfo",
	0x06: "authenticatorClientPIN",
	0x07: "authenticatorReset",
	0x08: "authenticatorGetNextAssertion(legacy)",
	0x09: "authenticatorBioEnrollment",
	0x0A: "authenticatorCredentialManagement",
	0x0B: "authenticatorSelection",
	0x0C: "authenticatorLargeBlobs",
	0x0D: "authenticatorConfig",
}
var ctapErrorCodes = map[byte]string{
	0x00: "CTAP1_ERR_SUCCESS",
	0x01: "CTAP1_ERR_INVALID_COMMAND",
	0x02: "CTAP1_ERR_INVALID_PARAMETER",
	0x03: "CTAP1_ERR_INVALID_LENGTH",
	0x04: "CTAP1_ERR_INVALID_SEQ",
	0x05: "CTAP1_ERR_TIMEOUT",
	0x06: "CTAP1_ERR_CHANNEL_BUSY",
	0x0A: "CTAP1_ERR_LOCK_REQUIRED",
	0x0B: "CTAP1_ERR_INVALID_CHANNEL",
	0x11: "CTAP2_ERR_CBOR_UNEXPECTED_TYPE",
	0x12: "CTAP2_ERR_INVALID_CBOR",
	0x14: "CTAP2_ERR_MISSING_PARAMETER",
	0x15: "CTAP2_ERR_LIMIT_EXCEEDED",
	0x17: "CTAP2_ERR_UNSUPPORTED_EXTENSION",
	0x19: "CTAP2_ERR_CREDENTIAL_EXCLUDED",
	0x21: "CTAP2_ERR_PROCESSING",
	0x22: "CTAP2_ERR_INVALID_CREDENTIAL",
	0x23: "CTAP2_ERR_USER_ACTION_PENDING",
	0x24: "CTAP2_ERR_OPERATION_PENDING",
	0x25: "CTAP2_ERR_NO_OPERATIONS",
	0x26: "CTAP2_ERR_UNSUPPORTED_ALGORITHM",
	0x27: "CTAP2_ERR_OPERATION_DENIED",
	0x28: "CTAP2_ERR_KEY_STORE_FULL",
	0x29: "CTAP2_ERR_NOT_BUSY",
	0x2A: "CTAP2_ERR_NO_OPERATION_PENDING",
	0x2B: "CTAP2_ERR_UNSUPPORTED_OPTION",
	0x2C: "CTAP2_ERR_INVALID_OPTION",
	0x2D: "CTAP2_ERR_KEEPALIVE_CANCEL",
	0x2E: "CTAP2_ERR_NO_CREDENTIALS",
	0x2F: "CTAP2_ERR_USER_ACTION_TIMEOUT",
	0x30: "CTAP2_ERR_NOT_ALLOWED",
	0x31: "CTAP2_ERR_PIN_INVALID",
	0x32: "CTAP2_ERR_PIN_BLOCKED",
	0x33: "CTAP2_ERR_PIN_AUTH_INVALID",
	0x34: "CTAP2_ERR_PIN_AUTH_BLOCKED",
	0x35: "CTAP2_ERR_PIN_NOT_SET",
	0x36: "CTAP2_ERR_PIN_REQUIRED",
	0x37: "CTAP2_ERR_PIN_POLICY_VIOLATION",
	0x38: "CTAP2_ERR_PIN_TOKEN_EXPIRED",
	0x39: "CTAP2_ERR_REQUEST_TOO_LARGE",
	0x3A: "CTAP2_ERR_ACTION_TIMEOUT",
	0x3B: "CTAP2_ERR_UP_REQUIRED",
	0x3C: "CTAP2_ERR_UV_BLOCKED",
	0x3D: "CTAP2_ERR_INTEGRITY_FAILURE",
	0x3E: "CTAP2_ERR_INVALID_SUBCOMMAND",
	0x3F: "CTAP2_ERR_UV_INVALID",
	0x40: "CTAP2_ERR_UNAUTHORIZED_PERMISSION",
	0x7F: "CTAP1_ERR_OTHER",
}
var webauthnExtensions = map[string]string{
	"appid":                             "FIDO AppID (U2F compatibility) extension",
	"appidExclude":                      "Exclude credentials matching AppID",
	"txAuthSimple":                      "Transaction authorization (simple prompt)",
	"txAuthGeneric":                     "Transaction authorization (generic content)",
	"authnSel":                          "Authenticator selection extension",
	"exts":                              "Supported extensions enumeration",
	"uvi":                               "User verification index",
	"loc":                               "Location extension",
	"uvm":                               "User verification method",
	"credProtect":                       "Credential protection policy",
	"credBlob":                          "Opaque credential blob storage",
	"largeBlobKey":                      "Large blob key",
	"minPinLength":                      "Minimum PIN length",
	"hmac-secret":                       "HMAC secret extension (prf predecessor)",
	"prf":                               "Pseudo-random function extension",
	"payment":                           "Secure Payment Confirmation hints",
	"credentialProtectionPolicy":        "CredProtect policy (CTAP2)",
	"enforceCredentialProtectionPolicy": "Enforce credProtect",
	"credProps":                         "Credential properties (rk residancy)",
	"largeBlob":                         "Large blob read/write",
	"devicePubKey":                      "Device public key (backing keys)",
}
var getInfoOptions = map[string]string{
	"plat":                           "platform authenticator",
	"rk":                             "supports resident/discoverable keys",
	"clientPin":                      "supports client PIN",
	"up":                             "supports user presence",
	"uv":                             "supports built-in user verification",
	"pinUvAuthToken":                 "supports pinUvAuthToken",
	"noMcGaPermissionsWithClientPin": "PIN token limited permissions",
	"largeBlobs":                     "supports large blobs",
	"ep":                             "enterprise attestation",
	"bioEnroll":                      "biometric enrollment",
	"userVerificationMgmtPreview":    "UV management preview",
	"uvBioEnroll":                    "UV required for bio enroll",
	"uvAcfg":                         "UV required for authnr config",
	"credMgmt":                       "credential management",
	"credentialMgmtPreview":          "cred mgmt preview",
	"setMinPINLength":                "set minimum PIN length",
	"makeCredUvNotRqd":               "makeCred without UV",
	"alwaysUv":                       "always require UV",
}

// ---------------------------------------------------------------------------
// Help & Usage  (interactive menu [H])
// Page 1: in-app guide (what the tool does, every menu option, tips).
// Page 2: the full command-line reference (same text as --help).
// ---------------------------------------------------------------------------

type owlHelpItem struct{ key, text string }

func owlHelpWrap(s string, width int) []string {
	var out []string
	for _, para := range strings.Split(s, "\n") {
		words := strings.Fields(para)
		if len(words) == 0 {
			out = append(out, "")
			continue
		}
		cur := ""
		for _, w := range words {
			if cur != "" && len([]rune(cur))+1+len([]rune(w)) > width {
				out = append(out, cur)
				cur = w
			} else if cur == "" {
				cur = w
			} else {
				cur += " " + w
			}
		}
		out = append(out, cur)
	}
	return out
}

func owlHelpTitle(t string) {
	fmt.Println()
	fmt.Println("  " + col("▸ "+t, B+CY))
}

func owlHelpPara(lines []string) {
	for _, l := range lines {
		for _, w := range owlHelpWrap(l, 60) {
			fmt.Println("    " + col(w, W))
		}
	}
}

func owlHelpRows(items []owlHelpItem) {
	kw := 0
	for _, it := range items {
		if n := len([]rune(it.key)); n > kw {
			kw = n
		}
	}
	for _, it := range items {
		k := "[" + it.key + "]" + strings.Repeat(" ", kw-len([]rune(it.key)))
		for i, w := range owlHelpWrap(it.text, 56-kw) {
			if i == 0 {
				fmt.Println("    " + col(k, YLW+B) + "  " + col(w, W))
			} else {
				fmt.Println("    " + strings.Repeat(" ", kw+2) + "  " + col(w, W))
			}
		}
	}
}

func owlHelpRule() { fmt.Println(col(strings.Repeat("─", 66), CY)) }

func tuiHelp() {
	clear()
	banner()
	owlHelpRule()
	fmt.Println("  " + col("⬡  Help & Usage — "+APPNAME, B+CY))
	owlHelpRule()
	owlHelpTitle("WHAT IT DOES")
	owlHelpPara(owlHelpAbout)
	owlHelpTitle("HOW TO USE THE MENU")
	owlHelpPara(owlHelpFlow)
	owlHelpTitle("MENU OPTIONS")
	owlHelpRows(owlHelpMenu)
	owlHelpTitle("TIPS")
	owlHelpRows(owlHelpTips)
	fmt.Println()
	owlHelpRule()
	fmt.Println("  " + col("Next page: command-line flags & copy-paste examples", DIM))
	pause()
	clear()
	owlHelpCLI()
	fmt.Println()
	fmt.Println("  " + col("Tip: the same reference is printed by  "+APPNAME+" --help", DIM))
	pause()
}

var owlHelpAbout = []string{
	"OFIDO verifies and audits WebAuthn / FIDO2 (passkey and security-key) ceremonies, the way a relying party (your website's server) should. It decodes the attestationObject, clientDataJSON and authenticatorData and checks origin, RP ID hash, challenge, user-presence / user-verification flags and sign counter. It verifies the signature with real cryptography (ES256, RS256, EdDSA ...) and checks attestation formats (packed, tpm, android-key, apple, fido-u2f, none) against trust roots and the FIDO Metadata Service.",
	"It can also audit your server's registration / login options, a database export of stored credentials and a key's getInfo. It can generate signed test ceremonies (good and malicious) to test your own server.",
}

var owlHelpFlow = []string{
	"Type the number of an option and press Enter. Set your expected origin and RP ID once with [4] Policy. The menu header shows the current origin, and every later verification is checked against it. Most inputs accept a file path, hex or base64. [H] opens this help, [0] or a blank line quits.",
}

var owlHelpMenu = []owlHelpItem{
	{"1", "Verify a response JSON: give a file with the PublicKeyCredential JSON the browser sent (registration or login). For a login, also give the stored credential key or the earlier registration JSON so the signature can be checked (blank = skip the signature)."},
	{"2", "Verify a registration: give the attestationObject and, optionally, the clientDataJSON. Shows the new credential, its attestation format and trust result, the device model (AAGUID) and findings."},
	{"3", "Verify a login: give authenticatorData, clientDataJSON, the signature, the stored public key (or registration JSON) and the stored signCount (blank = 0). A counter that does not increase hints at a cloned key."},
	{"4", "Policy: set the expected origin, RP ID, expected challenge, whether user verification is required, whether synced passkeys are rejected, and attestation trust roots (PEM). Blank keeps a value, - clears it."},
	{"5", "Audit RP options: give your server's creation / request options JSON and, optionally, the site origin. Flags weak settings (short challenge, wrong rpId, no UV ...)."},
	{"6", "Audit credential store: give a CSV / JSON export of stored credentials. Flags weak algorithms, counter problems, duplicates and revoked models."},
	{"7", "Analyse getInfo: give a CTAP2 getInfo response (blank = demo key) to see what that security key supports and can enforce."},
	{"8", "Generate RP test vectors: choose an output folder (blank = ofido-vectors) and your site origin. Writes signed good ceremonies and malicious ones (wrong origin, replayed challenge ...) that your server must reject."},
	{"9", "Decode CBOR: give CBOR as a file, hex or base64. Prints it in readable diagnostic notation."},
	{"10", "Parse a COSE key: give a COSE / PEM key, attestation object or registration JSON. Shows key type, algorithm, curve and whether it is usable."},
	{"11", "Look up an AAGUID: enter an AAGUID to see the authenticator model (built-in list, or the MDS from [12])."},
	{"12", "Load FIDO MDS blob: load a downloaded FIDO Metadata Service blob for models, attestation roots and status reports such as revoked or compromised devices."},
	{"13", "Reference: choose a topic: flags, formats, algs, ctap, extensions, getinfo, aaguids or flow."},
	{"14", "Export last report: choose txt, md, json, csv or sarif and an output file (blank = print to screen)."},
	{"15", "Run demo: a registration, a good login and a phished login (wrong origin) are verified."},
	{"16", "Self-test: real keys, every attestation format, and fuzzing."},
}

var owlHelpTips = []owlHelpItem{
	{"*", "Origin must match exactly: https://example.com is not https://www.example.com and not http://example.com."},
	{"*", "Copy the response JSON from your browser's dev tools (Network tab) or log it on your server, then use [1]."},
	{"*", "The MDS blob is free to download from fidoalliance.org (mds3.fidoalliance.org)."},
}

func owlHelpCLI() { usage() }
