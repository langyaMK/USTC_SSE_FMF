def counter(prefix, start=0, step=1):
    n = start
    while True:
        yield f"_{prefix}_{n}"
        n += step
