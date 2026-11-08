import sys, json
for l in sys.stdin:
    try: r = json.loads(l)
    except Exception: print(l.strip()); continue
    o = r.get('official', {}); m = r.get('ocaml4lean', {})
    oa = o.get('accept'); ma = m.get('accept')
    print('%-42s exp=%-6s ours=%-5s off=%-5s ok=%-5s ours=%-7s off=%-8s %s' % (
        r['test'], r.get('expected'), ma, oa, r.get('ok'),
        ('%.3f' % m['check_time']) if m.get('check_time') is not None else '-',
        ('%.3f' % o['kernel_time']) if o.get('kernel_time') is not None else '-',
        (r.get('error', '') or r.get('skipped', '') or ('' if r.get('ok', True) else m.get('msg', '')))[:70]))
